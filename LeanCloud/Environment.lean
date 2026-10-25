import LeanCloud.BlobStorage

namespace LeanCloud
open Lean

/-- Configured local concurrency and memory budgets, not instantaneous utilization. -/
structure WorkerCapacity where
  id : String := "local"
  cpus : Nat := 1
  memoryMiB : Option Nat := none
  deriving Repr, BEq, ToJson, FromJson, Inhabited

instance : Codec WorkerCapacity := jsonCodec _ "worker-capacity/v1"

/-- Live context of the executing attempt. Capabilities are local to `exec` and
are never serialized. Explicitly return any capacity data needed for planning. -/
structure Environment (m : Type → Type u) where
  currentWorker : WorkerCapacity := {}
  workers : Array WorkerCapacity := #[{}]
  blobs : BlobStorage m

def Environment.map (f : {α : Type} → m α → n α) (environment : Environment m) : Environment n :=
  { currentWorker := environment.currentWorker, workers := environment.workers,
    blobs := environment.blobs.map f }

/-- The interpreter supplies typed failures, including in pure models. `exec`
converts these capabilities to the user's base monad at its exception boundary. -/
abbrev ExecContext (m : Type → Type u) := Environment (ExceptT CloudError m)

end LeanCloud
