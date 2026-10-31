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
  /-- A shared counter is a replicated snapshot, never a sum of worker counters.
  Its revision orders snapshots independently of worker clocks. -/
  shared : Option String := none
  revision : Nat := 0
  deriving Repr, BEq, ToJson

instance : FromJson ProgressUpdate where
  fromJson? json := do
    return { message := ← json.getObjValAs? String "message"
             completed := ← json.getObjValAs? Nat "completed"
             total := ← json.getObjValAs? (Option Nat) "total"
             shared := (json.getObjValAs? String "shared").toOption
             revision := (json.getObjValAs? Nat "revision").toOption.getD 0 }

/-- Durable, deduplicated settlements. Failed work is included in completed. -/
structure WorkQueueProgress where
  completed : Nat := 0
  failed : Nat := 0
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
Keys are unique within one run-scoped queue. Reusing a key requires equal data
and priority. Higher priorities are received first. -/
structure WorkItem where
  key : String
  value : Json
  priority : Nat := 0
  deriving ToJson

instance : FromJson WorkItem where
  fromJson? json := do
    let fields ← json.getObj?
    return { key := ← json.getObjValAs? String "key"
             value := ← json.getObjVal? "value"
             priority := ← match fields["priority"]? with
               | none => pure 0
               | some value => fromJson? value }

/-- Stable position in priority-descending, submission-ascending order. -/
structure WorkPosition where
  priority : Nat
  sequence : Nat
  deriving Repr, BEq, ToJson, FromJson

/-- An observation of available work, without a lease or ownership. -/
structure WorkPreview where
  position : WorkPosition
  value : Json
  deriving ToJson, FromJson

/-- A durable completion announcement. Every observer has its own cursor;
reading this feed neither dequeues work nor changes another observer's position. -/
structure WorkCompletion where
  cursor : Nat
  value : Json
  failed : Bool
  deriving Repr, ToJson, FromJson, Inhabited

/-- Competing consumers with renewable leases. Duplicate deliveries are allowed.
Receipts fence expired deliveries; settlement never deletes a newer lease.
Broker waiting is bounded; an empty batch is not completion.
Transport errors are errors, never empty batches. -/
structure WorkQueue (m : Type → Type u) where
  send : Array WorkItem → m Unit
  /-- Highest priority first, FIFO for ties. Only available work is leased. -/
  receive : Nat → m (Array WorkDelivery)
  /-- Read available work in receive order without leasing it. A cursor continues
  strictly after that position, even if its item was removed. Pages are live,
  not a snapshot: restart at `none` to see new work ahead of the cursor. -/
  peek : Option WorkPosition → Nat → m (Array WorkPreview)
  /-- No messages remain, including leased messages. This is not a completion
  guarantee unless the application has finished producing work. -/
  isIdle : m Bool
  acknowledge : String → m Unit
  /-- Settle with an application outcome, atomically updating queue progress. -/
  complete : String → Bool → m Unit
  progress : m WorkQueueProgress
  completions : Nat → Nat → m (Array WorkCompletion)
  renew : String → m Unit
  release : String → m Unit

def WorkQueue.map (f : {α : Type} → m α → n α) (queue : WorkQueue m) : WorkQueue n where
  send values := f (queue.send values)
  receive count := f (queue.receive count)
  peek after count := f (queue.peek after count)
  isIdle := f queue.isIdle
  acknowledge receipt := f (queue.acknowledge receipt)
  complete receipt failed := f (queue.complete receipt failed)
  progress := f queue.progress
  completions after count := f (queue.completions after count)
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
    peek _ _ := unavailable
    isIdle := unavailable
    acknowledge _ := unavailable
    complete _ _ := unavailable
    progress := unavailable
    completions _ _ := unavailable
    renew _ := unavailable
    release _ := unavailable }⟩

end LeanCloud
