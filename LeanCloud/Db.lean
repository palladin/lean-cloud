import Lean

universe u

namespace LeanCloud
open Lean

/-- Execution records indexed by interpreter locations. Models can keep the
records in `σ`; real backends can thread an unchanged connection handle. -/
structure Db (σ : Type) (m : Type → Type u) where
  get : String → StateT σ m (Option Json)
  put : String → Json → StateT σ m Bool

end LeanCloud
