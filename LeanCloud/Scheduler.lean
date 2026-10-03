import LeanCloud.Coordination

/-! The scheduler is the sole writer of coordination state. It never executes
Cloud code or reads replay values. Its state is saved locally before replying.
Each actor has its own durable mailbox. Redelivery may repeat requests and
reports. Attempt numbers reject stale reports after reassignment. -/

namespace LeanCloud.Scheduler
open Lean

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

/-- Confirmed global records written/read by a worker process. These are hints
for placement and observability, not a second authority for replay values. -/
structure WorkerInfo where
  worker : WorkerId
  recorded : Array String := #[]
  deriving Repr, BEq, Inhabited, ToJson, FromJson

structure State where
  jobs : Array Job := #[⟨Location.root, Location.root, false, .pending⟩]
  workers : Array WorkerInfo := #[]
  nextAttempt : Nat := 0
  now : Nat := 0
  error : Option CloudError := none
  deriving Repr, BEq, ToJson, FromJson

def State.finished (state : State) : Bool :=
  state.jobs.any fun job => job.branch == Location.root && job.status == .done

-- Stable internal names allow proofs to use the deployed state transitions.
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

def awaken (state : State) : State :=
  { state with jobs := state.jobs.map fun job =>
      match job.status with
      | .waiting children =>
        if children.all (fun child => state.jobs.any (fun j => j.branch == child && j.status == .done)) then
          { job with status := .pending, joining := true }
        else job
      | _ => job }

def assignment (job : Job) (attempt : Nat) : Assignment :=
  ⟨attempt, job.branch, job.location, job.joining⟩

/-- Locate an existing assignment when a worker repeats its request. -/
def assignedTo (worker : WorkerId) (job : Job) : Option Assignment :=
  match job.status with
  | .running owner attempt _ =>
    if owner == worker then some (assignment job attempt) else none
  | _ => none

def acquire (state : State) (worker : WorkerId) (duration : Nat) : State × WorkerMessage := Id.run do
  if let some error := state.error then return (state, .failed error)
  if state.finished then return (state, .finished)
  -- The same request can be delivered twice, including after a lost reply.
  if let some existing := state.jobs.findSome? (assignedTo worker) then
    return (state, .execute existing)
  let some index := state.jobs.findIdx? (fun job => job.status == .pending)
    | return (state, .idle)
  let job := state.jobs[index]!
  let attempt := state.nextAttempt
  let jobs := state.jobs.set! index { job with status := .running worker attempt (state.now + max 1 duration) }
  return ({ state with jobs, nextAttempt := attempt + 1 }, .execute (assignment job attempt))

/-- Add each child at most once. Existing jobs retain their state and new jobs
start pending; inserting children never manufactures a completed branch. -/
def addChildren (jobs : Array Job) (children : Array Location) : Array Job :=
  children.foldl (fun jobs child =>
    if jobs.any (fun job => job.branch == child) then jobs
    else jobs.push ⟨child, child, false, .pending⟩) jobs

def accept (state : State) (report : Report) : State := Id.run do
  let state := observe state report.worker report.recorded
  let some index := state.jobs.findIdx? (fun job => match job.status with
      | .running worker attempt _ => worker == report.worker && attempt == report.attempt
      | _ => false) | return state
  let job := state.jobs[index]!
  match report.progress with
  | .error error => return { state with error := some error }
  | .ok .done =>
    return awaken { state with jobs := state.jobs.set! index { job with status := .done } }
  | .ok (.fork location count) =>
    -- A resumed branch may reach a later fork. Child keys contain that fork's
    -- full location; retries can never allocate a second copy of the children.
    let children := (Array.range count).map location.child
    let jobs := state.jobs.set! index { job with location, joining := false, status := .waiting children }
    return awaken { state with jobs := addChildren jobs children }

end Internal
open Internal

/-- One serial mailbox transition, with no backend operations. Persist the
returned state before delivering its messages. A lost reply is safe to retry. -/
def handle (duration : Nat) (state : State) (message : SchedulerMessage) : State × Array Delivery :=
  match message with
  | .ready worker =>
    let (state, response) := acquire (observe state worker #[]) worker duration
    (state, #[⟨worker, response⟩])
  | .report report =>
    (accept state report, #[⟨report.worker, .acknowledged report.attempt⟩])
  | .inspect replyTo => (state, #[⟨replyTo, .status (toJson state)⟩])
  | .tick elapsed =>
    let now := state.now + elapsed
    ({ state with now, jobs := state.jobs.map fun job =>
        match job.status with
        | .running _ _ deadline => if deadline ≤ now then { job with status := .pending } else job
        | _ => job }, #[])

end LeanCloud.Scheduler
