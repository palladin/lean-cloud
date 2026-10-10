import LeanCloud.Scheduler.Program

/-! The inbox handler drives the recursive scheduling program. Tickets and its
continuation are volatile. Jobs are an inspection view, never the source of
scheduling decisions. Recovery discards the continuation and starts at the root
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

structure Pending where
  ticket : Ticket
  branchStart : Location
  status : Status := .pending
  reply : Option (Except CloudError Progress) := none
  deriving Inhabited

structure State extends Snapshot where
  continuation : Waiting := suspend (run [Location.root]).run
  pending : Array Pending := #[]
  nextTicket : Nat := 0
  stopping : Array WorkerId := #[]
  barrier : Nat := 0

/-- The durable part contains no traversal, tickets, leases or branch tree. -/
structure Catalog where
  nextAttempt : Nat := 0
  workers : Array WorkerInfo := #[]
  error : Option CloudError := none
  deriving ToJson, FromJson

def State.catalog (state : State) : Catalog :=
  ⟨state.nextAttempt, state.workers.map (fun worker => { worker with recorded := #[] }), state.error⟩

def Catalog.restore (catalog : Catalog) : State :=
  { nextAttempt := catalog.nextAttempt, workers := catalog.workers, error := catalog.error }

-- JSON carries observations only, never executable continuations or tickets.
instance : ToJson State := ⟨fun state => toJson state.toSnapshot⟩
instance : Repr State := ⟨fun state prec => reprPrec state.toSnapshot prec⟩

/-- Completion as shown to clients; snapshots contain no executable state. -/
def Snapshot.finished (snapshot : Snapshot) : Bool :=
  snapshot.jobs.any fun job => job.branch == Location.root && job.status == .done

def State.finished (state : State) : Bool :=
  match state.continuation with
  | .done (.ok _) => true
  | _ => false

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

/-- Run pure scheduling code until it awaits a missing reply. The mailbox loop
remains free to serve other runs and administrative requests. -/
partial def advance (state : State) : State :=
  match state.continuation with
  | .done result => { state with error := match result with | .ok _ => none | .error error => some error }
  | .spawn branch next =>
    let ticket := state.nextTicket
    let state := view state branch fun job => { job with status := .pending }
    advance { state with
      pending := state.pending.push ⟨ticket, branch, .pending, none⟩
      nextTicket := ticket + 1
      continuation := next ticket }
  | .await ticket next =>
    match state.pending.find? (·.ticket == ticket) with
    | some task => match task.reply with
      | some reply => advance { state with
          continuation := next reply
          pending := state.pending.filter (·.ticket != ticket) }
      | none => state
    | none => { state with error := some ⟨.protocol, "Unknown scheduling ticket"⟩ }

def owned (state : State) (worker : WorkerId) : Option Assignment :=
  state.pending.findSome? fun task => match task.status with
    | .running owner attempt _ => if owner == worker then some ⟨attempt, task.branchStart⟩ else none
    | _ => none

def acquire (state : State) (worker : WorkerId) (duration : Nat) : State × WorkerMessage := Id.run do
  if state.stopping.contains worker then return (state, .cancel state.barrier)
  if !state.stopping.isEmpty then return (state, .idle)
  if let some error := state.error then return (state, .failed error)
  let state := advance state
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
  if !state.stopping.isEmpty then return state
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
  -- Arrival order does not change the recursive program's result order.
  let state := { state with
    pending := state.pending.set! index { task with status := .done, reply := some report.progress } }
  match report.progress with
  | .error error => return { state with error := some error }
  | .ok _ => return advance state

end Internal

/-- Recovery uses no saved traversal. Attempt IDs remain monotone so old reports
cannot satisfy a new ticket. The caller must first stop the old workers. -/
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
