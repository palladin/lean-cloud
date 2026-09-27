import LeanCloud.Core

namespace LeanCloud
open Lean

/-- Only outcomes and partial groups are stored; computations remain local. -/
inductive Result where
  | completed (outcome : Exit)
  | suspended (children : Array (Option Exit))
  deriving Repr, BEq, ToJson, FromJson

namespace Result

/-- Parallel resumes once every child has a result, in the original array order. -/
def settle (children : Array (Option Exit)) : Result :=
  match children.mapM id with
  | none => .suspended children
  | some outcomes =>
    match outcomes.mapM (fun outcome => match outcome with
      | .success value => Except.ok value
      | outcome => Except.error outcome) with
    | .ok values => .completed (.success (Json.arr values))
    | .error outcome => .completed outcome

def recordChild (result : Result) (index : Nat) (outcome : Exit) : Except CloudError Result := do
  match result with
  | .completed _ => return result
  | .suspended children =>
    if index ≥ children.size then throw ⟨.protocol, "Child is outside the suspended group"⟩
    if let some existing := children[index]! then
      if existing == outcome then return result
      throw ⟨.divergence, "Child completion changed during replay"⟩
    return settle (children.set! index (some outcome))

end Result

end LeanCloud
