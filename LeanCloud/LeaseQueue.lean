import LeanCloud.WorkQueue
import LeanCloud.Db
import LeanCloud.BlobStorage

namespace LeanCloud

/-- The transport primitives needed by a replay worker. Receipts belong to
deliveries, not locations; duplicate messages may carry the same location.
Successful enqueue must be durable before returning. Dequeue retains work until
acknowledgement, and unacknowledged leases must permit eventual redelivery.
Backend failures escape through `m`; a rejected receipt returns `false`.
Lease duration, renewal, waiting, and time belong to the backend environment. -/
structure LeaseQueue (σ : Type) (m : Type → Type) (ρ : Type) where
  enqueue : Location → StateT σ m Unit
  dequeue : StateT σ m (Option (Location × ρ))
  acknowledge : ρ → StateT σ m Bool

namespace LeaseQueue

/-- A worker's backend handle and its current delivery. On restart, use a fresh
worker with no receipt while retaining the durable Db and transport state. -/
structure Worker (σ ρ : Type) where
  backend : σ
  delivery : Option (Location × ρ) := none

def liftBackend [Monad m] (action : StateT σ m α) : StateT (Worker σ ρ) m α :=
  fun worker => do
    let (value, backend) ← action worker.backend
    return (value, { worker with backend })

def db [Monad m] (backend : Db σ m) : Db (Worker σ ρ) m where
  get key := liftBackend (backend.get key)
  put key value := liftBackend (backend.put key value)

def blobs [Monad m] (backend : BlobStorage σ m) : BlobStorage (Worker σ ρ) m where
  putBlob bytes := liftBackend (backend.putBlob bytes).run
  readBlob ref := liftBackend (backend.readBlob ref).run
  resolveBlob name := liftBackend (backend.resolveBlob name).run

/-- Adapt leased transport to the existing replay loop. `readCompleted` and
`writeCompleted` access a durable, run-scoped result in the Db, not the transport.
Writing an outcome must persist it before returning; retries of that same
outcome are idempotent, and a recorded outcome must not be cleared or changed.

Completion publishes each successor before acknowledging the current receipt.
A crash can leave any prefix of those enqueues committed. Retrying a location
must reconstruct and republish its work; duplicate deliveries are expected.
Publishing the final result also precedes acknowledgement. A completed restart
can return that result even if an old queue message remains unacknowledged.

Call `complete` only for the item returned by this worker's most recent `next`.
Other calls are ignored, preserving the current delivery. A rejected stale ack
does not undo publication: the transport retains the message for redelivery.
This adapter does not satisfy the stronger atomic `Proofs.QueueContract` law. -/
def toWorkQueue [Monad m] (queue : LeaseQueue σ m ρ)
    (readCompleted : StateT σ m (Option Exit))
    (writeCompleted : Exit → StateT σ m Unit) : WorkQueue (Worker σ ρ) m where
  next := do
    modify fun worker => { worker with delivery := none }
    if let some outcome ← liftBackend readCompleted then
      return .completed outcome
    match ← liftBackend queue.dequeue with
    | none => return .idle
    | some (location, receipt) =>
      modify fun worker => { worker with delivery := some (location, receipt) }
      return .item location
  complete location response := do
    let some (delivered, receipt) := (← get).delivery | return ()
    if delivered != location then return ()
    match response with
    | .runnable locations =>
      for next in locations do liftBackend (queue.enqueue next)
    | .done outcome => liftBackend (writeCompleted outcome)
    let _ ← liftBackend (queue.acknowledge receipt)
    modify fun worker => { worker with delivery := none }

end LeaseQueue
end LeanCloud
