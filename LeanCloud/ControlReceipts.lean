import LeanCloud.Pool

namespace LeanCloud.ControlReceipts
open Lean

structure Receipt where
  id : String
  command : Pool.Command
  result : Except String Json
  deriving ToJson, FromJson

/-- Only administrative mutations use durable receipts. Worker heartbeats,
readiness and inspection never grow this table. -/
def supported : Pool.Command → Bool
  | .pause _ | .resume _ | .kill _ | .remove _ => true
  | _ => false

/-- Persist the returned catalog and receipts together before replying. A retry
after another command or a scheduler restart returns its original result; it
does not reapply an old intent. Request IDs remain reserved for this deployment. -/
def apply (state : Pool.State) (receipts : Array Receipt) (id : String) (command : Pool.Command) :
    Pool.State × Array Receipt × Except String Json :=
  if !supported command then (state, receipts, .error "Operation does not support control receipts")
  else match receipts.find? (·.id == id) with
  | some receipt =>
    (state, receipts, if toJson receipt.command == toJson command then receipt.result
      else .error "Request ID already belongs to a different command")
  | none =>
    let (state, result) := match Pool.command state command with
      | .ok (state, result) => (state, .ok result)
      | .error error => (state, .error error)
    (state, receipts.push ⟨id, command, result⟩, result)

end LeanCloud.ControlReceipts
