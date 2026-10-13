import Lean

namespace LeanCloud
open Lean

/-- Operational limits; they do not change Cloud semantics or replay keys. -/
structure ExecutionConfig where
  interpreterFuel : Nat := 100000
  deriving Repr, BEq, ToJson, Inhabited

def ExecutionConfig.validate (config : ExecutionConfig) : Except String Unit := do
  unless config.interpreterFuel > 0 do throw "worker.interpreterFuel must be positive"

instance : FromJson ExecutionConfig where
  fromJson? json := do
    let object ← json.getObj?
    let field (name : String) (fallback : Nat) :=
      match object[name]? with
      | none => pure fallback
      | some value => fromJson? value
    let config : ExecutionConfig := {
      interpreterFuel := ← field "interpreterFuel" 100000 }
    config.validate
    return config

end LeanCloud
