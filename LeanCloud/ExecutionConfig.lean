import Lean

namespace LeanCloud
open Lean

/-- Operational limits; they do not change Cloud semantics or replay keys. -/
structure ExecutionConfig where
  interpreterFuel : Nat := 100000
  retryDelayMs : Nat := 500
  retryMaxDelayMs : Nat := 5000
  deriving Repr, BEq, ToJson, Inhabited

def ExecutionConfig.validate (config : ExecutionConfig) : Except String Unit := do
  unless config.interpreterFuel > 0 do throw "worker.interpreterFuel must be positive"
  unless config.retryDelayMs > 0 do throw "worker.retryDelayMs must be positive"
  unless config.retryDelayMs ≤ config.retryMaxDelayMs && config.retryMaxDelayMs ≤ 60000 do
    throw "worker.retryMaxDelayMs must be between retryDelayMs and 60000"

instance : FromJson ExecutionConfig where
  fromJson? json := do
    let object ← json.getObj?
    let field (name : String) (fallback : Nat) :=
      match object[name]? with
      | none => pure fallback
      | some value => fromJson? value
    let config : ExecutionConfig := {
      interpreterFuel := ← field "interpreterFuel" 100000
      retryDelayMs := ← field "retryDelayMs" 500
      retryMaxDelayMs := ← field "retryMaxDelayMs" 5000 }
    config.validate
    return config

/-- First retry uses the initial delay; later retries back off to the cap.
Bound the exponent even for a worker that has been retrying for days. -/
def ExecutionConfig.retryWaitMs (config : ExecutionConfig) (retry : Nat) : UInt32 :=
  (min config.retryMaxDelayMs (config.retryDelayMs * 2 ^ min retry 16)).toUInt32

end LeanCloud
