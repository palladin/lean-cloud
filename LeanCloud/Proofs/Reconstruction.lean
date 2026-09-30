import LeanCloud.Proofs.TreeRouting

/-! Structural fuel bounds for reconstruction through the original program. -/

namespace LeanCloud.Proofs
open Lean

/-- Reconstruction fuel depends on the original route, not on which durable
records a previous attempt managed to commit. The target has its own budget. -/
def TreeRoute.prefixSteps {tree current target node} : TreeRoute tree current target node → Nat
  | .terminal .. | .fork .. => 0
  | .delay rest | .next rest | .child _ rest => rest.prefixSteps + 1

/-- A single finite budget covers every reconstruction path, independently of
delivery order and the journal left by previous attempts. -/
theorem TreeRoute.fuel_bound {tree current target node} (route : TreeRoute tree current target node) :
    route.prefixSteps + 1 ≤ sizeOf tree := by
  induction route with
  | terminal => simp [prefixSteps]
  | fork => simp [prefixSteps]; omega
  | delay rest ih => simp only [prefixSteps]; simp_wf; omega
  | next rest ih => simp only [prefixSteps]; simp_wf; omega
  | @child children result next current target node index rest ih =>
    have smaller := List.sizeOf_lt_of_mem (List.getElem_mem index.isLt)
    simp only [prefixSteps]
    simp_wf
    omega

end LeanCloud.Proofs
