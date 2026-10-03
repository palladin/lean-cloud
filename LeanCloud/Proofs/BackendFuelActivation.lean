import LeanCloud.Proofs.BackendFuelExecution

namespace LeanCloud.Backend.Proofs.Fuel
open Lean LeanEff LeanCloud.Proofs Execution Iteration

def extend (mapping : Nat → Nat) (index value : Nat) : Nat → Nat :=
  fun id => if id = index then value else mapping id

theorem Related.activate [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after)
    (owner : Owner) (left : Backend.M Outcome) (right : Backend.M (Answer α))
    (inside : owner.worker < before.workers.size)
    (follows : Follows (FuelStopped Worker.exhausted)
      (fun returned => Program.ofEff (resume (remaining owner.worker) source returned))
      (Program.ofEff left) (Program.ofEff right)) :
    ∃ lastMap, Related remaining source lastMap
      (Execution.activate owner left before) (Execution.activate owner right after) := by
  have targetInside : owner.worker < after.workers.size := by rw [← same.size]; exact inside
  cases left with
  | pure value =>
    refine ⟨mapping, ?_⟩
    constructor
    · simpa only [activate_preserves] using same.services
    · cases right <;> simpa only [Execution.activate, Array.size_setIfInBounds] using same.size
    · intro index worker held
      by_cases equal : owner.worker = index
      · subst index
        simp only [Execution.activate, Array.getElem?_setIfInBounds_self, inside] at held
        cases held
        change FuelStopped Worker.exhausted value ∨ _
        by_cases stopped : FuelStopped Worker.exhausted value
        · exact .inl stopped
        · exact .inr (by
            rw [← follows.returned_eq stopped]
            exact activate_continues after owner right targetInside)
      · have old : before.workers[index]? = some worker := by
          simpa only [Execution.activate, Array.getElem?_setIfInBounds, equal, ↓reduceIte] using held
        exact (same.workers index worker old).frame (Nat.le_refl _) (fun _ _ => rfl)
          (activate_other equal) (fun id call stored =>
            (activate_old_call (Array.getElem?_eq_some_iff.mp stored).choose).trans stored)
    · intro id call held
      obtain ⟨current, stored, related⟩ := same.calls id call held
      exact ⟨current, (activate_old_call (Array.getElem?_eq_some_iff.mp stored).choose).trans stored, related⟩
    · exact same.injective
  | impure operation next =>
    cases right with
    | pure value => cases follows
    | impure other rest =>
      cases follows with
      | request operation left right nextSame =>
        let lastMap := extend mapping before.calls.size after.calls.size
        have oldMap : ∀ id, id < before.calls.size → lastMap id = mapping id := by
          intro id bounded
          simp [lastMap, extend, Nat.ne_of_lt bounded]
        refine ⟨lastMap, ?_⟩
        constructor
        · exact same.services
        · simpa only [Execution.activate, Array.size_setIfInBounds] using same.size
        · intro index worker held
          by_cases equal : owner.worker = index
          · subst index
            simp only [Execution.activate, Array.getElem?_setIfInBounds_self, inside] at held
            cases held
            exact ⟨by simp [Execution.activate], by simp [Execution.activate, targetInside, lastMap, extend]⟩
          · have old : before.workers[index]? = some worker := by
              simpa only [Execution.activate, Array.getElem?_setIfInBounds, equal, ↓reduceIte] using held
            exact (same.workers index worker old).frame (by simp [Execution.activate]) oldMap
              (activate_other equal) (fun id call stored =>
                (activate_old_call (Array.getElem?_eq_some_iff.mp stored).choose).trans stored)
        · intro id call held
          change (before.calls.push _)[id]? = some call at held
          rw [Array.getElem?_push] at held
          split at held
          · rename_i equal
            subst id
            cases held
            exact ⟨.pending owner operation (some rest), by simp [Execution.activate, lastMap, extend],
              .pending _ _ (.live nextSame)⟩
          · have bounded := (Array.getElem?_eq_some_iff.mp held).choose
            obtain ⟨current, stored, related⟩ := same.calls id call held
            refine ⟨current, ?_, related⟩
            rw [oldMap id bounded]
            exact (activate_old_call (Array.getElem?_eq_some_iff.mp stored).choose).trans stored
        · intro first last firstInside lastInside equal
          change first < (before.calls.push _).size at firstInside
          change last < (before.calls.push _).size at lastInside
          simp only [Array.size_push] at firstInside lastInside
          by_cases atFirst : first = before.calls.size
          · subst first
            by_cases atLast : last = before.calls.size
            · exact atLast.symm
            · have lastOld : last < before.calls.size := by omega
              have mapped := same.mapped_inside lastOld
              simp only [lastMap, extend, ↓reduceIte, atLast] at equal
              omega
          · have firstOld : first < before.calls.size := by omega
            by_cases atLast : last = before.calls.size
            · subst last
              have mapped := same.mapped_inside firstOld
              simp only [lastMap, extend, ↓reduceIte, atFirst] at equal
              omega
            · exact same.injective first last firstOld (by omega)
                (by simpa [lastMap, extend, atFirst, atLast] using equal)

end LeanCloud.Backend.Proofs.Fuel
