import LeanCloud.Mailbox

/-! A deployment owns a persistent pool. Each run has its own volatile recursive
scheduling program; the pool routes replies and chooses which run gets the next
free worker. Replay values remain in the run's global blob namespace. -/
namespace LeanCloud.Pool
open Lean

inductive Mode where
  | active | paused | killed
  deriving Repr, BEq, ToJson, FromJson

structure Run where
  id : String
  mode : Mode := .active
  scheduler : Scheduler.State := {}
  /-- A terminal intent is published by a leased worker, just like ordinary work. -/
  finalization : Scheduler.Status := .pending
  deriving Repr, ToJson

/-- A generation fences delayed drain acknowledgements after a worker rejoins.
`none` is the unrestricted, pre-configuration pool. -/
structure Membership where
  active : Option (Array String) := none
  generation : Nat := 0
  drained : Array String := #[]
  deriving Repr, ToJson, FromJson

structure State where
  runs : Array Run := #[]
  cursor : Nat := 0
  membership : Membership := {}
  deriving Repr, ToJson

/-- Persistence contains administrative intent and counters, never observations
or the scheduler's executable continuation. -/
structure RunCatalog where
  id : String
  mode : Mode
  scheduler : Scheduler.Catalog
  finalization : Scheduler.Status := .pending
  deriving ToJson

structure Catalog where
  runs : Array RunCatalog := #[]
  cursor : Nat := 0
  membership : Membership := {}
  deriving ToJson

instance : FromJson RunCatalog where
  fromJson? json := do
    let finalization ← match json.getObjVal? "finalization" with
      | .ok value => fromJson? value
      | .error _ => pure Scheduler.Status.pending
    return {
      id := ← json.getObjValAs? String "id"
      mode := ← json.getObjValAs? Mode "mode"
      scheduler := ← json.getObjValAs? Scheduler.Catalog "scheduler"
      finalization }

instance : FromJson Catalog where
  fromJson? json := do
    let membership ← match json.getObjVal? "membership" with
      | .ok value => fromJson? value
      | .error _ => pure {}
    return { runs := ← json.getObjValAs? _ "runs", cursor := ← json.getObjValAs? Nat "cursor", membership }

def State.catalog (state : State) : Catalog :=
  { cursor := state.cursor, membership := state.membership
    runs := state.runs.map fun run =>
      { id := run.id, mode := run.mode, scheduler := run.scheduler.catalog
        finalization := if run.finalization == .done then .done else .pending } }

def Catalog.restore (catalog : Catalog) : State :=
  { cursor := catalog.cursor, membership := catalog.membership
    runs := catalog.runs.map fun run =>
      { id := run.id, mode := run.mode, scheduler := run.scheduler.restore
        finalization := if run.finalization == .done then .done else .pending } }

inductive Command where
  | health
  | configureWorkers (workers : Array String)
  | workers
  | workerStopped (worker : String) (generation : Nat)
  | submit (run : String)
  | pause (run : String)
  | resume (run : String)
  | kill (run : String)
  | status (run : String)
  | check (run worker : String) (attempt : Nat)
  deriving Repr, ToJson, FromJson

inductive Message where
  | submit (run : String)
  | ready (worker : String)
  | stopped (run worker : String) (barrier : Nat)
  | renew (run worker : String) (attempt : Nat)
  | drained (worker : String) (generation : Nat)
  | report (run : String) (report : Report)
  | request (replyTo : String) (command : Command)
  deriving Repr, ToJson, FromJson

inductive Reply where
  | execute (run : String) (assignment : Assignment)
  | finalize (run : String) (attempt : Nat) (outcome : Exit)
  | cancel (run : String) (barrier : Nat)
  | idle
  | acknowledged
  | drain (generation : Nat)
  deriving Repr, ToJson, FromJson

private def Run.cancel (run : Run) (workers : Array WorkerId := #[]) : Run :=
  let workers := match run.finalization with
    | .running owner _ _ => workers.push owner
    | _ => workers
  { run with scheduler := Scheduler.cancel run.scheduler workers
             finalization := match run.finalization with | .running .. => .pending | status => status }

/-- Only the run catalog survives. Old attempts stop before any root is replayed. -/
def recover (state : State) (workers : Array WorkerId := #[]) : State :=
  { state with runs := state.runs.map fun run =>
      run.cancel ((workers ++ state.membership.active.getD #[] ++ run.scheduler.workers.map (·.worker))
        |>.filter (!state.membership.drained.contains ·)) }

def stopped (state : State) (id worker : String) (barrier : Nat) : State :=
  { state with runs := state.runs.map fun run =>
      if run.id == id then { run with scheduler := Scheduler.stopped run.scheduler worker barrier } else run }

def tick (elapsed : Nat) (state : State) : State :=
  { state with runs := state.runs.map fun run =>
      let run := { run with scheduler := { run.scheduler with now := run.scheduler.now + elapsed } }
      let expired := Scheduler.expired run.scheduler || match run.finalization with
        | .running _ _ deadline => deadline ≤ run.scheduler.now
        | _ => false
      if run.scheduler.stopping.isEmpty && expired then run.cancel else run }

def Run.accepts (run : Run) : Bool :=
  run.mode == .active && run.scheduler.stopping.isEmpty && !run.scheduler.finished && run.scheduler.error.isNone

/-- Terminal outcomes requested by coordination. Workers publish these intents,
retrying after restart until the root is sealed.
An accepted failure precedes a later kill. An earlier root result always wins. -/
def Run.terminalOutcome (run : Run) : Option Exit :=
  match run.scheduler.error with
  | some error => some (.failure error)
  | none => if run.mode == .killed then some (.cancelled "Killed by user") else none

def valid (state : State) (id worker : String) (attempt : Nat) : Bool :=
  let owns := fun status => match status with
      | .running owner current _ => owner == worker && current == attempt
      | _ => false
  !state.membership.drained.contains worker && state.runs.any fun run => run.id == id &&
    (if !run.scheduler.stopping.isEmpty then false else if run.terminalOutcome.isSome then owns run.finalization
     else run.accepts && run.scheduler.pending.any fun task => owns task.status)

/-- A heartbeat extends only an existing attempt. It cannot revive expired or
revoked work. Retiring workers can finish their current assignment before drain. -/
def renew (duration : Nat) (state : State) (id worker : String) (attempt : Nat) : State :=
  if !valid state id worker attempt then state
  else { state with runs := state.runs.map fun run =>
    if run.id != id then run else
    let extend := fun status => match status with
      | .running owner current deadline =>
        if owner == worker && current == attempt then
          .running owner current (max deadline (run.scheduler.now + max 1 duration))
        else status
      | _ => status
    { run with
      finalization := extend run.finalization
      scheduler := Scheduler.mapAssignments run.scheduler extend } }

/-- Repeated readiness returns the existing assignment before allocating work
in another run. Run selection rotates; result order stays the program's order. -/
def acquire (duration : Nat) (state : State) (worker : String) : State × Reply := Id.run do
  for run in state.runs do
    if run.scheduler.stopping.contains worker then return (state, .cancel run.id run.scheduler.barrier)
  if let some active := state.membership.active then
    unless active.contains worker do return (state, .drain state.membership.generation)
  for run in state.runs do
    if let some outcome := run.terminalOutcome.filter (fun _ => run.scheduler.stopping.isEmpty) then
      if let .running owner attempt _ := run.finalization then
        if owner == worker then return (state, .finalize run.id attempt outcome)
    if run.accepts then
      if let some assignment := Scheduler.Internal.owned run.scheduler worker then
        return (state, .execute run.id assignment)
  for offset in [:state.runs.size] do
    let index := (state.cursor + offset) % state.runs.size
    let some run := state.runs[index]? | continue
    if let some outcome := run.terminalOutcome.filter (fun _ => run.scheduler.stopping.isEmpty) then
      if run.finalization == .pending then
        let attempt := run.scheduler.nextAttempt
        -- Recovery must stop terminal writers even without configured routes.
        let scheduler := Scheduler.Internal.observe run.scheduler worker #[]
        let run := { run with
          finalization := .running worker attempt (run.scheduler.now + max 1 duration)
          scheduler := { scheduler with nextAttempt := attempt + 1 } }
        return ({ state with runs := state.runs.set! index run, cursor := index + 1 },
          .finalize run.id attempt outcome)
    if run.accepts then
      let (scheduler, message) := Scheduler.Internal.acquire (Scheduler.Internal.observe run.scheduler worker #[]) worker duration
      if let .execute assignment := message then
        return ({ state with
          runs := state.runs.set! index { run with scheduler }
          cursor := index + 1 }, .execute run.id assignment)
  return (state, .idle)

/-- Sent by a serial worker only between assignments. Retiring does not revoke
its running work; this acknowledgement fences any queued duplicate assignments. -/
def drained (state : State) (worker : String) (generation : Nat) : State :=
  if generation != state.membership.generation ||
      state.membership.active.any (·.contains worker) || state.membership.active.isNone then state
  else
    let workers := if state.membership.drained.contains worker then state.membership.drained
      else state.membership.drained.push worker
    { state with
    membership := { state.membership with drained := workers },
    runs := state.runs.map fun run =>
      let owns := (Scheduler.runningWorkers run.scheduler).contains worker || match run.finalization with
        | .running owner _ _ => owner == worker
        | _ => false
      let run := if owns && run.scheduler.stopping.isEmpty then run.cancel else run
      { run with scheduler := Scheduler.stopped run.scheduler worker run.scheduler.barrier } }

def report (state : State) (id : String) (value : Report) : State :=
  { state with runs := state.runs.map fun run =>
      if run.id != id then run
      else if !run.scheduler.stopping.isEmpty then run
      else if run.terminalOutcome.isSome then
        match run.finalization, value.progress with
        | .running owner attempt _, .ok .done =>
          if owner == value.worker && attempt == value.attempt then
            { run with finalization := .done }
          else run
        | _, _ => run
      else if run.accepts then
        let scheduler := Scheduler.Internal.accept run.scheduler value
        -- Revoke every sibling before publishing a terminal failure.
        let run := { run with scheduler }
        if scheduler.error.isSome then run.cancel else run
      else run }

private def setMode (state : State) (id : String) (mode : Mode) : Except String State := do
  let some index := state.runs.findIdx? (·.id == id)
    | if mode == .killed then return { state with runs := state.runs.push { id, mode := .killed } }
      else throw s!"Unknown run: {id}"
  let some run := state.runs[index]? | throw "Missing run"
  if run.mode == .killed && mode != .killed then throw "Killed runs cannot be resumed or paused"
  if run.scheduler.error.isSome && mode != .killed then
    throw "Failed runs cannot be resumed or paused; submit a new run"
  let run := { run with mode }
  let run := if mode == .active || !run.scheduler.stopping.isEmpty then run else run.cancel
  return { state with runs := state.runs.set! index run }

/-- Administrative requests are serialized with assignment and report handling.
Pausing revokes attempts; resuming never reuses an attempt number. -/
def command (state : State) : Command → Except String (State × Json)
  | .health => .ok (state, Json.null)
  | .workers => .ok (state, toJson state.membership)
  | .workerStopped worker generation => .ok (drained state worker generation, Json.null)
  | .configureWorkers workers =>
    let membership := if state.membership.active == some workers then state.membership else
      { active := some workers, generation := state.membership.generation + 1,
        drained := state.membership.drained.filter (!workers.contains ·) }
    .ok ({ state with membership }, toJson membership)
  | .check id worker attempt => .ok (state, toJson (valid state id worker attempt))
  | .submit id =>
    let state := if state.runs.any (·.id == id) then state
      else { state with runs := state.runs.push { id } }
    .ok (state, Json.null)
  | .status id => do
    let some run := state.runs.find? (·.id == id) | throw s!"Unknown run: {id}"
    return (state, toJson run.scheduler)
  | .pause id => return (← setMode state id .paused, Json.null)
  | .resume id => return (← setMode state id .active, Json.null)
  | .kill id => return (← setMode state id .killed, Json.null)

end LeanCloud.Pool
