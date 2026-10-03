import LeanCloud.Proofs.BackendFuelRestart

namespace LeanCloud.Backend.Proofs.Fuel
open Lean LeanEff LeanCloud.Proofs Execution Iteration

/-- The repeated model starts its next iteration. The real loop has already
issued that request, so this administrative event requires no target event. -/
theorem Related.attach [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after) (linked : Linked before)
    (owner : Owner) (value : Outcome)
    (finished : before.workers[owner.worker]? = some ⟨owner.attempt, .finished value⟩)
    (left : Backend.M Outcome) (code : Program (Answer α)) (budget : Nat)
    (continued : Continues owner code after)
    (follows : Follows (FuelStopped Worker.exhausted)
      (fun returned => Program.ofEff (resume budget source returned)) (Program.ofEff left) code) :
    ∃ lastMap, Related (extend remaining owner.worker budget) source lastMap
      (Execution.activate owner left before) after := by
  have inside := (Array.getElem?_eq_some_iff.mp finished).choose
  have rebudget {id : Nat} {call : Call Outcome} (held : before.calls[id]? = some call) {current : Call (Answer α)}
      (related : CallFollows (α := α) remaining source call current) :
      CallFollows (extend remaining owner.worker budget) source call current := by
    apply related.rebudget
    intro caller live
    have different := Linked.inactive_caller linked finished (by intro _ impossible; cases impossible) held live
    simp [extend, different]
  cases left with
  | pure returned =>
    refine ⟨mapping, ?_⟩
    constructor
    · exact same.services
    · simpa only [Execution.activate, Array.size_setIfInBounds] using same.size
    · intro index worker held
      by_cases equal : owner.worker = index
      · subst index
        simp only [Execution.activate, Array.getElem?_setIfInBounds_self, inside] at held
        cases held
        change FuelStopped Worker.exhausted returned ∨ _
        by_cases stopped : FuelStopped Worker.exhausted returned
        · exact .inl stopped
        · apply Or.inr
          simpa only [extend, ↓reduceIte, follows.returned_eq stopped] using continued
      · have old := (activate_other equal).symm.trans held
        exact (same.workers index worker old).rebudget (by simp [extend, Ne.symm equal])
    · intro id call held
      obtain ⟨current, stored, related⟩ := same.calls id call held
      exact ⟨current, stored, rebudget held related⟩
    · exact same.injective
  | impure operation next =>
    obtain ⟨rest, codeEq, each⟩ := follows.request_view
    rw [codeEq] at continued
    obtain ⟨id, targetNext, waiting, restEq⟩ := continued.request_view
    let lastMap := extend mapping before.calls.size id
    have oldMap : ∀ id, id < before.calls.size → lastMap id = mapping id := by
      intro id bounded
      simp [lastMap, extend, Nat.ne_of_lt bounded]
    have fresh : ∀ other, other < before.calls.size → mapping other ≠ id := by
      intro other bounded
      exact same.future_distinct linked finished waiting bounded
    refine ⟨lastMap, ?_⟩
    constructor
    · exact same.services
    · simpa only [Execution.activate, Array.size_setIfInBounds] using same.size
    · intro index worker held
      by_cases equal : owner.worker = index
      · subst index
        simp only [Execution.activate, Array.getElem?_setIfInBounds_self, inside] at held
        cases held
        exact ⟨by simp [Execution.activate], by simpa only [lastMap, extend, ↓reduceIte] using waiting.1⟩
      · have old := (activate_other equal).symm.trans held
        have previous := (same.workers index worker old).rebudget
          (updated := extend remaining owner.worker budget) (by simp [extend, Ne.symm equal])
        exact previous.frame (by simp [Execution.activate]) oldMap rfl (fun _ _ held => held)
    · intro other call held
      change (before.calls.push _)[other]? = some call at held
      rw [Array.getElem?_push] at held
      split at held
      · rename_i equal
        subst other
        cases held
        refine ⟨.pending owner operation (some targetNext), ?_, .pending _ _ (.live ?_)⟩
        · simpa [lastMap, extend] using waiting.2
        · intro response
          simpa only [extend, ↓reduceIte, restEq] using each response
      · have bounded := (Array.getElem?_eq_some_iff.mp held).choose
        obtain ⟨current, stored, related⟩ := same.calls other call held
        exact ⟨current, by rw [oldMap other bounded]; exact stored, rebudget held related⟩
    · intro first last firstInside lastInside equal
      change first < (before.calls.push _).size at firstInside
      change last < (before.calls.push _).size at lastInside
      simp only [Array.size_push] at firstInside lastInside
      by_cases firstNew : first = before.calls.size
      · subst first
        by_cases lastNew : last = before.calls.size
        · exact lastNew.symm
        · have bounded : last < before.calls.size := by omega
          have different := fresh last bounded
          simp only [lastMap, extend, ↓reduceIte, lastNew] at equal
          exact False.elim (different equal.symm)
      · have bounded : first < before.calls.size := by omega
        by_cases lastNew : last = before.calls.size
        · subst last
          have different := fresh first bounded
          simp only [lastMap, extend, ↓reduceIte, firstNew] at equal
          exact False.elim (different equal)
        · exact same.injective first last bounded (by omega)
            (by simpa [lastMap, extend, firstNew, lastNew] using equal)

theorem Related.iterate [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after) (linked : Linked before)
    (traversal : Nat) (supported : PureProgram source) (index attempt budget : Nat)
    (held : before.workers[index]? = some ⟨attempt, .finished (.ok (.ok none, ⟨(), none⟩))⟩)
    (current : remaining index = budget + 1) (enough : traversal ≤ budget + 1) :
    ∃ lastMap, Related (extend remaining index budget) source lastMap
      (Execution.activate ⟨index, attempt⟩ (Iteration.program traversal source) before) after := by
  have previous := same.workers index _ held
  change FuelStopped Worker.exhausted (.ok (.ok none, ⟨(), none⟩) : Outcome) ∨ _ at previous
  rcases previous with stopped | continued
  · obtain ⟨handle, impossible⟩ := stopped
    cases impossible
  · have active : Continues ⟨index, attempt⟩ (Program.ofEff (loop (α := α) (budget + 1) source)) after := by
      simpa only [resume, current, loop] using continued
    exact same.attach linked ⟨index, attempt⟩ _ held (Iteration.program traversal source) _ budget active
      (Follows.entry traversal budget source supported enough)

end LeanCloud.Backend.Proofs.Fuel
