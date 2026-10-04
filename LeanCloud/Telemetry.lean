import LeanCloud.SourceInfo

namespace LeanCloud
open Lean

/-- Container counters sampled alongside an observation. Missing counters stay
missing. Monotonic time and incarnation fence rate calculations across restarts. -/
structure ResourceSample where
  incarnation : String
  timeNs : Nat
  cpuNs : Option Nat := none
  memory : Option Nat := none
  memoryLimit : Option Nat := none
  rx : Option Nat := none
  tx : Option Nat := none
  readBytes : Option Nat := none
  writeBytes : Option Nat := none
  diskUsed : Option Nat := none
  diskCapacity : Option Nat := none
  deriving ToJson, FromJson, Inhabited

/-- Best-effort observations, never an authority for execution or completion.
Sequence numbers are local to a worker incarnation, not a global clock. -/
structure ExecutionEvent where
  session : String
  seq : Nat
  elapsedMs : Nat
  worker : String
  attempt : Option Nat
  location : String
  activity : String
  operation : String
  run : String := ""
  source : Option SourceSiteId := none
  deriving ToJson, FromJson

end LeanCloud
