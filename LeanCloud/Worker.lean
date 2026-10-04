import LeanCloud.ReplayInterpreter
import LeanCloud.Mailbox

namespace LeanCloud.Worker

/-- Volatile state. The broker retains unacknowledged assignments and confirmed
reports across process failure, so the worker needs no local durable outbox. -/
structure State where
  stopped : Bool := false
  retryIn : Nat := 0

/-- Observe successful global reads/writes; report only their keys. -/
structure ObservedStore (m : Type → Type u) where
  records : ReplayStore m
  confirmed : m (Array String)

structure Ports (m : Type → Type u) where
  id : WorkerId
  inbox : Mailbox m WorkerMessage
  send : SchedulerMessage → m Unit
  observe : ObservedStore m
  blobs : BlobStorage m
  retryPolls : Nat := 16

def execute [Monad m] [Codec α] (id : WorkerId) (store : ObservedStore m)
    (blobs : BlobStorage m) (fuel : Nat) (program : ι → Cloud m α) (input : ι)
    (assignment : Assignment) (observer : Option (ReplayInterpreter.Observer m) := none) : m Report := do
  let progress ← (ReplayInterpreter.step store.records blobs fuel program input assignment observer).run
  return ⟨id, assignment.attempt, progress, ← store.confirmed⟩

/-- Finish an assignment by recording its values, publishing its report with a
broker confirmation, and only then acknowledging its delivery. A crash before
acknowledgement replays the assignment; duplicates reuse the immutable records. -/
def turn [Monad m] [Codec α] (ports : Ports m) (fuel : Nat)
    (program : ι → Cloud m α) (input : ι) (state : State)
    (observer : Option (ReplayInterpreter.Observer m) := none) : m State := do
  if state.stopped then return state
  let delivery ← ports.inbox.receive
  let mut state := { state with retryIn := state.retryIn - 1 }
  if let some delivery := delivery then
    match delivery.message with
    | .execute assignment =>
      let report ← execute ports.id ports.observe ports.blobs fuel program input assignment observer
      ports.send (.report report)
      state := { state with retryIn := max 1 ports.retryPolls }
    | .acknowledged _ => state := { state with retryIn := 0 }
    | .finished | .failed _ => state := { state with stopped := true }
    | _ => pure ()
    -- Publish any immediate successor before dropping the current delivery.
    if !state.stopped && state.retryIn == 0 then
      ports.send (.ready ports.id)
      state := { state with retryIn := max 1 ports.retryPolls }
    ports.inbox.acknowledge delivery.receipt
  else if state.retryIn == 0 then
    ports.send (.ready ports.id)
    state := { state with retryIn := max 1 ports.retryPolls }
  return state

end LeanCloud.Worker
