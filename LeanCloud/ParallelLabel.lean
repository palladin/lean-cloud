import Lean

namespace LeanCloud
open Lean

/-- Optional display text before and after a parallel group's children finish.
Labels never affect execution, replay records, or scheduling. -/
structure ParallelLabel where
  running : String := ""
  completed : String := ""
  deriving Inhabited, Repr, BEq, ToJson, FromJson

instance : Coe String ParallelLabel := ⟨fun text => { running := text }⟩

/-- The declared child count prevents an incomplete observation page from
making a group look finished. -/
structure ParallelDisplay where
  count : Nat
  label : ParallelLabel
  deriving Inhabited, Repr, BEq, ToJson, FromJson

end LeanCloud
