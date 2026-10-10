import LeanCloud.ReplayModel

namespace LeanCloud.ReplayFaults
open ReplayModel

inductive Side where
  | before | after
  deriving Repr, BEq, DecidableEq

inductive Operation where
  | read (key : String)
  | create (key : String)
  deriving Repr, BEq, DecidableEq

structure Fault where
  operation : Operation
  side : Side
  deriving Repr, BEq

/-- Test diagnostics survive retries. The next fault fires at the next matching
operation; unrelated operations pass without consuming it. -/
structure Faults where
  remaining : List Fault := []
  visited : Array Operation := #[]
  crashes : Nat := 0
  deriving Repr

structure State (δ : Type) where
  durable : δ
  faults : Faults := {}

/-- State survives interruption. `Side` is below the CloudError layer, so an
interpreter's workflow error handler cannot catch a crash. -/
abbrev M (δ : Type) := ExceptT Side (StateM (State δ))

def atomic (label : Operation) (operation : δ → α × δ) : M δ α := fun state =>
  let selected := state.faults.remaining.head?.filter (·.operation == label)
  let faults := { state.faults with
    remaining := if selected.isSome then state.faults.remaining.drop 1 else state.faults.remaining
    visited := state.faults.visited.push label
    crashes := state.faults.crashes + if selected.isSome then 1 else 0 }
  if selected.any (·.side == .before) then
    (.error .before, { state with faults })
  else
    let (value, durable) := operation state.durable
    let result := if selected.isSome then .error .after else .ok value
    (result, { durable, faults })

/-- Discard the interrupted continuation and start the same action again.
Only crashes are retried; successful results and Cloud errors both return. -/
def restart (actionFuel : Nat) (action : ExceptT Side (StateM σ) (Except CloudError α)) :
    StateM σ (Except CloudError α) := fun saved =>
  match actionFuel with
  | 0 => (.error ⟨.protocol, "Replay restart fuel exhausted"⟩, saved)
  | fuel + 1 =>
      let (result, saved) := action.run saved
      match result with
      | .ok result => (result, saved)
      | .error _ => restart fuel action saved

abbrev WorkerM := M Journal

def store : ReplayStore WorkerM where
  read key := atomic (.read key) (fun journal => (journal.lookup key, journal))
  create key record := atomic (.create key) (ReplayModel.store.create key record)

def noBlobs : BlobStorage WorkerM where
  putBlob _ := throw ⟨.unsupported, "User blobs are outside the pure replay model"⟩
  readBlob _ := throw ⟨.unsupported, "User blobs are outside the pure replay model"⟩
  resolveBlob _ := throw ⟨.unsupported, "User blobs are outside the pure replay model"⟩

/-- A completed worker returns the recorded outcome. Scheduling never reads the
journal to retrieve it. A suspended worker reports which children are needed. -/
inductive Report where
  | done (outcome : Exit)
  | fork (location : Location) (count : Nat)
  deriving Repr, BEq

/-- One attempt, including reading the durable result into the worker's reply. -/
def attempt [Codec α] (fuel : Nat) (program : ι → Cloud WorkerM α) (input : ι)
    (assignment : Assignment) : ExceptT CloudError WorkerM Report := do
  match ← ReplayInterpreter.step store noBlobs fuel program input assignment with
  | .fork location count => return .fork location count
  | .done =>
      let some outcome ← store.outcome assignment.branchStart
        | throw ⟨.protocol, "Completed worker has no recorded outcome"⟩
      return .done outcome

/-- The only restart boundary: retry one worker with its surviving records.
Each retry receives a fresh interpreter budget; the retry budget is separate. -/
def worker [Codec α] (retries fuel : Nat) (program : ι → Cloud WorkerM α) (input : ι)
    (assignment : Assignment) : StateM (State Journal) (Except CloudError Report) :=
  restart retries (attempt fuel program input assignment).run

structure Plan where
  workers : List (Location × List Fault) := []

/-- Storage and test diagnostics shared by the model backend. There is no
scheduler crash state, saved continuation, or restart position. -/
structure Saved where
  journal : Journal := []
  workers : List (Location × Faults) := []

def Saved.initial (plan : Plan := {}) : Saved :=
  { workers := plan.workers.map fun (branch, faults) => (branch, { remaining := faults }) }

abbrev Backend := ExceptT CloudError (StateM Saved)

/-- One local worker reply, with only its new records and retry diagnostics. -/
structure WorkerResult where
  assignment : Assignment
  result : Except CloudError Report
  records : Journal
  faults : Faults

def runWorker [Codec α] (source : Cloud WorkerM α) (fuel : Nat) (saved : Saved)
    (assignment : Assignment) : WorkerResult :=
  let localState : State Journal := ⟨saved.journal, (saved.workers.lookup assignment.branchStart).getD {}⟩
  let (result, finished) := (worker fuel fuel (fun _ : Unit => source) () assignment).run localState
  ⟨assignment, result, newRecords saved.journal finished.durable, finished.faults⟩

def saveFaults (workers : List (Location × Faults)) (reply : WorkerResult) : List (Location × Faults) :=
  (reply.assignment.branchStart, reply.faults) :: workers.filter (fun entry => entry.1 != reply.assignment.branchStart)

/-- All tasks have stopped before their records are merged. Errors are returned
only after the completed and interrupted workers' records have been retained. -/
def collectWorkers (saved : Saved) (replies : List WorkerResult) : Except CloudError (List (Assignment × Report)) × Saved :=
  let workers := replies.foldl saveFaults saved.workers
  match ReplayModel.merge saved.journal (replies.reverse.flatMap (·.records)) with
  | .error error => (.error error, { saved with workers })
  | .ok journal => (replies.mapM (fun reply => reply.result.map (reply.assignment, ·)), { journal, workers })

/-- The backend starts every worker with the same immutable old journal. Local
restarts happen inside the spawned function; only new records are returned.
Drain all tasks and union their disjoint writes before returning reports, even
if one worker has exhausted its budget. This models storage, not scheduler IO. -/
def workers [Codec α] (source : Cloud WorkerM α) (fuel : Nat) (assignments : List Assignment) :
    Backend (List (Assignment × Report)) := fun saved =>
  let tasks := assignments.map fun assignment =>
    Task.spawn fun () => runWorker source fuel saved assignment
  collectWorkers saved (tasks.map Task.get)

end LeanCloud.ReplayFaults
