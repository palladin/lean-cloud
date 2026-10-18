import LeanCloud.Protocol

namespace LeanCloud
open Lean

/-- Local concurrency and memory budgets, not instantaneous utilization or host
totals. `cpus` is at least one; an absent memory budget means unknown. -/
structure WorkerCapacity where
  id : String := "local"
  cpus : Nat := 1
  memoryMiB : Option Nat := none
  deriving Repr, BEq, ToJson, FromJson, Inhabited

/-- Execution context supplied by the handler. `exec` uses the executing attempt's
context; environment-based parallel planning records its context before forking.
Workers describe configured pool capacity, not idle or reserved workers. -/
structure Environment where
  currentWorker : WorkerCapacity := {}
  workers : Array WorkerCapacity := #[{}]
  deriving Repr, BEq, ToJson, FromJson, Inhabited

instance : Codec Environment := jsonCodec _ "environment/v1"

end LeanCloud
