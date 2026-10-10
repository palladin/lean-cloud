import LeanCloud.ReplayInterpreter
import LeanCloud.Mailbox

namespace LeanCloud.Worker

/-- Volatile state. The broker retains unacknowledged assignments and confirmed
reports across process failure, so the worker needs no local durable outbox. -/
structure State where
  stopped : Bool := false
  retryIn : Nat := 0
  cancelledThrough : Option Nat := none
  reported : Option Nat := none
  awaitingAck : Bool := false

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

/-- Publish a terminal coordination intent. Only a worker touches the root
record; an already published workflow outcome remains the winner. -/
def finalize [Monad m] (id : WorkerId) (store : ObservedStore m)
    (attempt : Nat) (outcome : Exit) : m Report := do
  let progress ← (ReplayInterpreter.Internal.finish store.records Location.root outcome).run
  return ⟨id, attempt, progress, ← store.confirmed⟩

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
      unless (state.cancelledThrough.any (assignment.attempt ≤ ·) || state.reported.any (assignment.attempt ≤ ·) : Bool) do
        let report ← execute ports.id ports.observe ports.blobs fuel program input assignment observer
        ports.send (.report report)
        state := { state with reported := some assignment.attempt, awaitingAck := true }
      state := { state with retryIn := max 1 ports.retryPolls }
    | .cancel barrier =>
      state := { state with
        retryIn := 0
        cancelledThrough := some (max barrier (state.cancelledThrough.getD 0)) }
      ports.send (.stopped ports.id barrier)
    | .acknowledged attempt =>
      if state.awaitingAck && state.reported == some attempt then
        state := { state with retryIn := 0, awaitingAck := false }
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
