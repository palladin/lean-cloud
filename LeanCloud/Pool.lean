import LeanCloud.Mailbox

/-! A deployment owns a persistent pool. Each run retains the ordinary scheduler
state machine; this coordinator only routes messages and chooses which run gets
the next free worker. Replay values remain in the run's global blob namespace. -/
namespace LeanCloud.Pool
open Lean

inductive Mode where
  | active | paused | killed
  deriving Repr, BEq, ToJson, FromJson

structure Run where
  id : String
  mode : Mode := .active
  scheduler : Scheduler.State := {}
  deriving Repr, ToJson, FromJson

structure State where
  runs : Array Run := #[]
  cursor : Nat := 0
  deriving Repr, ToJson, FromJson

inductive Command where
  | health
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
  | report (run : String) (report : Report)
  | request (replyTo : String) (command : Command)
  deriving Repr, ToJson, FromJson

inductive Reply where
  | execute (run : String) (assignment : Assignment)
  | idle
  | acknowledged
  deriving Repr, ToJson, FromJson

def release (state : Scheduler.State) : Scheduler.State :=
  { state with jobs := state.jobs.map fun job =>
      match job.status with
      | .running .. => { job with status := .pending }
      | _ => job }

def recover (state : State) : State :=
  { state with runs := state.runs.map fun run => { run with scheduler := release run.scheduler } }

def tick (elapsed : Nat) (state : State) : State :=
  { state with runs := state.runs.map fun run =>
      { run with scheduler := (Scheduler.handle 1 run.scheduler (.tick elapsed)).1 } }

def Run.accepts (run : Run) : Bool :=
  run.mode == .active && !run.scheduler.finished && run.scheduler.error.isNone

def valid (state : State) (id worker : String) (attempt : Nat) : Bool :=
  state.runs.any fun run => run.id == id && run.accepts &&
    run.scheduler.jobs.any fun job => match job.status with
      | .running owner current _ => owner == worker && current == attempt
      | _ => false

/-- Repeated readiness returns the existing assignment before allocating work
in another run. Run selection rotates; result order stays the program's order. -/
def acquire (duration : Nat) (state : State) (worker : String) : State × Reply := Id.run do
  for run in state.runs do
    if run.accepts then
      if let some assignment := run.scheduler.jobs.findSome? (Scheduler.Internal.assignedTo worker) then
        return (state, .execute run.id assignment)
  for offset in [:state.runs.size] do
    let index := (state.cursor + offset) % state.runs.size
    let some run := state.runs[index]? | continue
    if run.accepts then
      let (scheduler, message) := Scheduler.Internal.acquire run.scheduler worker duration
      if let .execute assignment := message then
        return ({ state with
          runs := state.runs.set! index { run with scheduler }
          cursor := index + 1 }, .execute run.id assignment)
  return (state, .idle)

def report (state : State) (id : String) (value : Report) : State :=
  { state with runs := state.runs.map fun run =>
      if run.id == id && run.accepts then
        { run with scheduler := Scheduler.Internal.accept run.scheduler value }
      else run }

private def setMode (state : State) (id : String) (mode : Mode) : Except String State := do
  let some index := state.runs.findIdx? (·.id == id)
    | if mode == .killed then return { state with runs := state.runs.push ⟨id, .killed, {}⟩ }
      else throw s!"Unknown run: {id}"
  let some run := state.runs[index]? | throw "Missing run"
  if run.mode == .killed && mode != .killed then throw "Killed runs cannot be resumed or paused"
  let scheduler := if mode == .active then run.scheduler else release run.scheduler
  return { state with runs := state.runs.set! index { run with mode, scheduler } }

/-- Administrative requests are serialized with assignment and report handling.
Pausing revokes attempts; resuming never reuses an attempt number. -/
def command (state : State) : Command → Except String (State × Json)
  | .health => .ok (state, Json.null)
  | .check id worker attempt => .ok (state, toJson (valid state id worker attempt))
  | .submit id =>
    let state := if state.runs.any (·.id == id) then state
      else { state with runs := state.runs.push ⟨id, .active, {}⟩ }
    .ok (state, Json.null)
  | .status id => do
    let some run := state.runs.find? (·.id == id) | throw s!"Unknown run: {id}"
    return (state, toJson run.scheduler)
  | .pause id => return (← setMode state id .paused, Json.null)
  | .resume id => return (← setMode state id .active, Json.null)
  | .kill id => return (← setMode state id .killed, Json.null)

end LeanCloud.Pool
