import LeanCloud.Execution

namespace LeanCloud
open Lean

/-- Read-only attempt cancellation. The runtime owns and signals the source. -/
structure CancellationToken (m : Type → Type u) where
  isRequested : m Bool

structure ProgressUpdate where
  message : String := ""
  completed : Nat := 0
  total : Option Nat := none
  deriving Repr, BEq, ToJson, FromJson

/-- Absolute, best-effort last views. A slot identifies a local activity, not a
replay location. Reporting must be safe from concurrent local tasks. -/
structure ProgressReporter (m : Type → Type u) where
  report : String → ProgressUpdate → m Unit

structure WorkDelivery where
  receipt : String
  value : Json
  deriving ToJson, FromJson, Inhabited

/-- A stable application key makes publication safe to repeat, even after ACK.
Keys are unique within one run-scoped queue. Reusing a key requires equal data. -/
structure WorkItem where
  key : String
  value : Json
  deriving ToJson, FromJson

/-- Competing consumers with renewable leases. Duplicate deliveries are allowed.
Receipts fence expired deliveries; settlement never deletes a newer lease.
Broker waiting is bounded; an empty batch is not completion.
Transport errors are errors, never empty batches. -/
structure WorkQueue (m : Type → Type u) where
  send : Array WorkItem → m Unit
  receive : Nat → m (Array WorkDelivery)
  /-- No messages remain, including leased messages. This is not a completion
  guarantee unless the application has finished producing work. -/
  isIdle : m Bool
  acknowledge : String → m Unit
  renew : String → m Unit
  release : String → m Unit

def WorkQueue.map (f : {α : Type} → m α → n α) (queue : WorkQueue m) : WorkQueue n where
  send values := f (queue.send values)
  receive count := f (queue.receive count)
  isIdle := f queue.isIdle
  acknowledge receipt := f (queue.acknowledge receipt)
  renew receipt := f (queue.renew receipt)
  release receipt := f (queue.release receipt)

/-- Names are scoped to the workflow run by the runtime. Opening is idempotent. -/
structure QueueProvider (m : Type → Type u) where
  «open» : String → WorkQueue m

/-- Explicit adapters for models and standalone runners that do not host work queues. -/
def CancellationToken.never [Pure m] : CancellationToken m := ⟨pure false⟩
def ProgressReporter.ignore [Pure m] : ProgressReporter m := ⟨fun _ _ => pure ()⟩
def QueueProvider.unsupported [Monad m] [MonadExceptOf CloudError m] : QueueProvider m :=
  let unavailable {α : Type} : m α := throw ⟨.unsupported, "Work queues are not configured"⟩
  ⟨fun _ => {
    send _ := unavailable
    receive _ := unavailable
    isIdle := unavailable
    acknowledge _ := unavailable
    renew _ := unavailable
    release _ := unavailable }⟩

end LeanCloud
