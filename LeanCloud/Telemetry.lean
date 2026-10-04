import Lean.Data.Json

namespace LeanCloud
open Lean

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
  deriving ToJson, FromJson

end LeanCloud
