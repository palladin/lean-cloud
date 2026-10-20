import LeanCloud.Scheduler.Program

/-! The inbox handler drives the recursive scheduling program. Branch callbacks
and group joins are volatile. Jobs are an inspection view, never the source of
scheduling decisions. Recovery discards the callbacks and starts at the root
only after the pool has cancelled and drained the old attempts. -/

namespace LeanCloud.Scheduler
open Lean LeanEff

inductive Status where
  | pending
  | running (worker : WorkerId) (attempt deadline : Nat)
  | waiting (children : Array Location)
  | done
  deriving Repr, BEq, Inhabited, ToJson, FromJson

structure Job where
  branch : Location
  location : Location
  joining : Bool := false
  status : Status := .pending
  deriving Repr, BEq, Inhabited, ToJson, FromJson

structure WorkerInfo where
  worker : WorkerId
  recorded : Array String := #[]
  deriving Repr, BEq, Inhabited, ToJson, FromJson

/-- An observational snapshot for status, traces and timings. -/
structure Snapshot where
  jobs : Array Job := #[⟨Location.root, Location.root, false, .pending⟩]
  workers : Array WorkerInfo := #[]
  nextAttempt : Nat := 0
  now : Nat := 0
  error : Option CloudError := none
  deriving Repr, BEq, ToJson, FromJson

/-- A group counts unfinished callbacks, including callbacks suspended in
nested groups. Its continuation resumes in the enclosing group. -/
structure Group where
  id : Nat
  parent : Option Nat
  remaining : Nat
  next : Unit → Waiting
  deriving Inhabited

structure Pending where
  group : Nat
  branchStart : Location
  status : Status := .pending
  next : Progress → Waiting
  deriving Inhabited

structure State extends Snapshot where
  started : Bool := false
  groups : Array Group := #[]
  pending : Array Pending := #[]
  nextGroup : Nat := 0
  stopping : Array WorkerId := #[]
  barrier : Nat := 0

/-- The durable part contains no callbacks, groups, leases or branch tree. -/
structure Catalog where
  nextAttempt : Nat := 0
  workers : Array WorkerInfo := #[]
  error : Option CloudError := none
  deriving ToJson, FromJson

def State.catalog (state : State) : Catalog :=
  ⟨state.nextAttempt, state.workers.map (fun worker => { worker with recorded := #[] }), state.error⟩

def Catalog.restore (catalog : Catalog) : State :=
  { nextAttempt := catalog.nextAttempt, workers := catalog.workers, error := catalog.error }

-- JSON carries observations only, never executable callbacks or groups.
instance : ToJson State := ⟨fun state => toJson state.toSnapshot⟩
instance : Repr State := ⟨fun state prec => reprPrec state.toSnapshot prec⟩

/-- Completion as shown to clients; snapshots contain no executable state. -/
def Snapshot.finished (snapshot : Snapshot) : Bool :=
  snapshot.jobs.any fun job => job.branch == Location.root && job.status == .done

def State.finished (state : State) : Bool :=
  state.started && state.groups.isEmpty && state.pending.isEmpty && state.error.isNone

namespace Internal

def observe (state : State) (worker : WorkerId) (keys : Array String) : State := Id.run do
  let mut workers := state.workers
  match workers.findIdx? (fun info => info.worker == worker) with
  | none => workers := workers.push ⟨worker, keys⟩
  | some index =>
    let info := workers[index]!
    let recorded := keys.foldl (fun all key => if all.contains key then all else all.push key) info.recorded
    workers := workers.set! index { info with recorded }
  return { state with workers }

private def view (state : State) (branch : Location) (update : Job → Job) : State :=
  let index := state.jobs.findIdx? (·.branch == branch)
  let job := update (index.map (state.jobs[·]!) |>.getD ⟨branch, branch, false, .pending⟩)
  { state with jobs := match index with
      | some index => state.jobs.set! index job
      | none => state.jobs.push job }

/-- Handle one callback until it finishes or dispatches a group. Completing
the last callback removes its group before invoking the group's continuation.
No other branch's reply is needed to advance this callback. -/
partial def advance (state : State) (parent : Option Nat) : Waiting → State
  | .done =>
    match parent with
    | none => state
    | some id =>
      match state.groups.findIdx? (·.id == id) with
      | none => { state with error := some ⟨.protocol, "Unknown scheduling group"⟩ }
      | some index =>
        let group := state.groups[index]!
        if group.remaining > 1 then
          { state with groups := state.groups.set! index { group with remaining := group.remaining - 1 } }
        else
          advance { state with groups := state.groups.eraseIdxIfInBounds index } group.parent (group.next ())
  | .forEach branches body next => Id.run do
    if branches.isEmpty then return advance state parent (next ())
    let id := state.nextGroup
    let mut state := { state with
      groups := state.groups.push ⟨id, parent, branches.size, next⟩
      nextGroup := id + 1 }
    for branch in branches do
      state := view state branch fun job => { job with status := .pending }
      state := { state with pending := state.pending.push ⟨id, branch, .pending, body branch⟩ }
    return state

def owned (state : State) (worker : WorkerId) : Option Assignment :=
  state.pending.findSome? fun task => match task.status with
    | .running owner attempt _ => if owner == worker then some ⟨attempt, task.branchStart⟩ else none
    | _ => none

def acquire (state : State) (worker : WorkerId) (duration : Nat) : State × WorkerMessage := Id.run do
  if state.stopping.contains worker then return (state, .cancel state.barrier)
  if !state.stopping.isEmpty then return (state, .idle)
  if let some error := state.error then return (state, .failed error)
  let state := if state.started then state else
    advance { state with started := true } none (suspend (run #[Location.root]))
  if let some error := state.error then return (state, .failed error)
  if state.finished then return (state, .finished)
  if let some existing := owned state worker then return (state, .execute existing)
  let some index := state.pending.findIdx? (fun task => task.status == .pending)
    | return (state, .idle)
  let task := state.pending[index]!
  let attempt := state.nextAttempt
  let status := Status.running worker attempt (state.now + max 1 duration)
  let state := view state task.branchStart fun job => { job with status }
  return ({ state with pending := state.pending.set! index { task with status }, nextAttempt := attempt + 1 },
    .execute ⟨attempt, task.branchStart⟩)

def accept (state : State) (report : Report) : State := Id.run do
  if !state.stopping.isEmpty || state.error.isSome then return state
  let some index := state.pending.findIdx? (fun task => match task.status with
      | .running worker attempt _ => worker == report.worker && attempt == report.attempt
      | _ => false) | return state
  let task := state.pending[index]!
  let state := observe state report.worker report.recorded
  let state := view state task.branchStart fun job => match report.progress with
    | .error _ => job
    | .ok .done => { job with status := .done }
    | .ok (.fork location count) =>
      { job with location, joining := true, status := .waiting ((Array.range count).map location.child) }
  -- Consume ownership before calling the callback: duplicate reports cannot
  -- run it twice. Workers still collect workflow results in source order.
  let state := { state with pending := state.pending.eraseIdxIfInBounds index }
  match report.progress with
  | .error error => return { state with error := some error }
  | .ok progress => return advance state (some task.group) (task.next progress)

end Internal

/-- Recovery uses no saved traversal. Attempt IDs remain monotone so old reports
cannot satisfy a new assignment. The caller must first stop the old workers. -/
private def restart (state : State) : State :=
  { nextAttempt := state.nextAttempt, now := state.now, error := state.error, workers := state.workers }

def runningWorkers (state : State) : Array WorkerId :=
  state.pending.foldl (fun all task => match task.status with
    | .running worker _ _ => if all.contains worker then all else all.push worker
    | _ => all) #[]

/-- Cancellation is a barrier, not lease expiry. No replacement is dispatched
until every old owner has acknowledged stopping (or its process was stopped). -/
def cancel (state : State) (workers : Array WorkerId := #[]) : State :=
  let stopping := (workers ++ runningWorkers state ++ state.stopping).foldl
    (fun all worker => if all.contains worker then all else all.push worker) (#[] : Array WorkerId)
  let state := { state with stopping, barrier := state.nextAttempt, nextAttempt := state.nextAttempt + 1 }
  let state := { state with jobs := state.jobs.map fun job => match job.status with
    | .running .. => { job with status := .pending }
    | _ => job }
  if stopping.isEmpty then restart state else state

def stopped (state : State) (worker : WorkerId) (barrier : Nat) : State :=
  if barrier != state.barrier || !state.stopping.contains worker then state else
  let state := { state with stopping := state.stopping.filter (· != worker) }
  if state.stopping.isEmpty then restart state else state

def expired (state : State) : Bool := state.pending.any fun task => match task.status with
  | .running _ _ deadline => deadline ≤ state.now
  | _ => false

/-- Renew transport assignments without touching the scheduling program. -/
def mapAssignments (state : State) (update : Status → Status) : State :=
  { state with pending := state.pending.map fun task => { task with status := update task.status }
               jobs := state.jobs.map fun job => { job with status := update job.status } }

def handle (duration : Nat) (state : State) (message : SchedulerMessage) : State × Array Delivery :=
  match message with
  | .ready worker =>
    let (state, response) := Internal.acquire (Internal.observe state worker #[]) worker duration
    (state, #[⟨worker, response⟩])
  | .report report =>
    (Internal.accept state report, #[⟨report.worker, .acknowledged report.attempt⟩])
  | .stopped worker barrier => (stopped state worker barrier, #[])
  | .tick elapsed =>
    let state := { state with now := state.now + elapsed }
    (if state.stopping.isEmpty && expired state then cancel state else state, #[])

end LeanCloud.Scheduler
