import LeanCloud.Result
import Init.Data.Array.Monadic

/-! Laws for the actual parallel-result bookkeeping used by replay.
These cover fresh child slots. Idempotence of repeated successful completions is
not proved here: the existing equality check delegates to Lean's partial JSON
comparison. Recovery proofs will need a separate treatment of that comparison. -/

namespace LeanCloud.Result
open Lean

private theorem list_collect_missing {α : Type} :
    (values : List (Option α)) → none ∈ values → values.mapM id = none
  | [], missing => by simp at missing
  | none :: _, _ => by simp [List.mapM_cons]
  | some value :: rest, missing => by
    have missingRest : none ∈ rest := by simpa using missing
    simp [List.mapM_cons, list_collect_missing rest missingRest]

/-- A group waits for every child, even if an already finished child failed. -/
theorem settle_missing (children : Array (Option Exit)) (missing : none ∈ children) :
    settle children = .suspended children := by
  have collect : children.mapM id = none := by
    rw [Array.mapM_eq_mapM_toList, list_collect_missing children.toList (by simpa using missing)]
    rfl
  simp [settle, collect]

/-- Once all children have outcomes, result selection uses their array order. -/
theorem settle_completed (outcomes : Array Exit) :
    settle (outcomes.map some) =
      match outcomes.mapM (fun outcome => match outcome with
        | .success value => Except.ok value
        | outcome => Except.error outcome) with
      | .ok values => .completed (.success (Json.arr values))
      | .error outcome => .completed outcome := by
  have collect : (outcomes.map some).mapM id = some outcomes := by
    simp only [Array.mapM_map, Function.comp_def, id_eq]
    simpa [pure] using (Array.mapM_pure (m := Option) (xs := outcomes) (f := id))
  simp only [settle, collect]
  rfl

theorem settle_successes (values : Array Json) :
    settle ((values.map Exit.success).map some) = .completed (.success (Json.arr values)) := by
  rw [settle_completed]
  simp only [Array.mapM_map, Function.comp_def]
  have collect : values.mapM (fun value => (Except.ok value : Except Exit Json)) = .ok values := by
    simpa [pure, Except.pure] using (Array.mapM_pure (m := Except Exit) (xs := values) (f := id))
  rw [collect]

theorem settle_empty : settle #[] = .completed (.success (Json.arr #[])) := by
  simpa using settle_successes #[]

/-- Earlier successes cannot mask the first failure, and later results cannot
replace it. All children in this statement have already completed. -/
theorem settle_first_failure (successes : Array Json) (error : CloudError) (suffix : Array Exit) :
    settle ((successes.map Exit.success ++ #[Exit.failure error] ++ suffix).map some) =
      .completed (.failure error) := by
  rw [settle_completed]
  simp only [Array.mapM_append, Array.mapM_map, Function.comp_def]
  have collect : successes.mapM (fun value => (Except.ok value : Except Exit Json)) = .ok successes := by
    simpa [pure, Except.pure] using (Array.mapM_pure (m := Except Exit) (xs := successes) (f := id))
  rw [collect]
  simp [Array.mapM_eq_mapM_toList, pure, Except.pure]
  rfl

private theorem settle_suspended_children {children updated : Array (Option Exit)}
    (suspended : settle children = .suspended updated) : updated = children := by
  unfold settle at suspended
  split at suspended
  · exact (Result.suspended.inj suspended).symm
  · split at suspended <;> cases suspended

theorem recordChild_completed (existing : Exit) (index : Nat) (outcome : Exit) :
    recordChild (.completed existing) index outcome = .ok (.completed existing) := rfl

theorem recordChild_out_of_bounds (children : Array (Option Exit)) (index : Nat)
    (outcome : Exit) (outside : children.size ≤ index) :
    recordChild (.suspended children) index outcome =
      .error ⟨.protocol, "Child is outside the suspended group"⟩ := by
  simp [recordChild, outside]
  rfl

theorem recordChild_missing (children : Array (Option Exit)) (index : Nat) (outcome : Exit)
    (inside : index < children.size) (missing : children[index]! = none) :
    recordChild (.suspended children) index outcome =
      .ok (settle (children.set! index (some outcome))) := by
  simp [recordChild, Nat.not_le_of_lt inside, missing]
  rfl

/-- While a group remains suspended, recording a fresh child fills exactly its
slot, preserves the array size, and leaves every other slot unchanged. -/
theorem recordChild_preserves_slots (children : Array (Option Exit)) (index : Nat) (outcome : Exit)
    (inside : index < children.size) (missing : children[index]! = none)
    (updated : Array (Option Exit))
    (recorded : recordChild (.suspended children) index outcome = .ok (.suspended updated)) :
    updated.size = children.size ∧ updated[index]! = some outcome ∧
      ∀ other, index ≠ other → updated[other]! = children[other]! := by
  rw [recordChild_missing children index outcome inside missing] at recorded
  have equal := settle_suspended_children (Except.ok.inj recorded)
  subst updated
  exact ⟨Array.size_set! _ _ _, Array.getElem!_set!_self _ _ _ inside,
    fun other different => Array.getElem!_set!_ne _ _ _ _ different⟩

/-- Finishing one child cannot settle a group while a different slot is empty. -/
theorem settle_waits_for_other (children : Array (Option Exit)) (index other : Nat)
    (outcome : Exit) (inside : other < children.size) (different : index ≠ other)
    (missing : children[other]! = none) :
    settle (children.set! index (some outcome)) =
      .suspended (children.set! index (some outcome)) := by
  apply settle_missing
  have emptySlot : (children.set! index (some outcome))[other]! = none := by
    rw [Array.getElem!_set!_ne _ _ _ _ different, missing]
  have valid : other < (children.set! index (some outcome)).size := by simpa using inside
  rw [getElem!_pos (children.set! index (some outcome)) other valid] at emptySlot
  exact Array.mem_of_getElem emptySlot

/-- Filling the only remaining slot produces precisely the expected ordered
array of outcomes, including failures. -/
theorem fill_last_slot (children : Array (Option Exit)) (outcomes : Array Exit)
    (size : children.size = outcomes.size) (index : Fin outcomes.size)
    (others : ∀ other (inside : other < children.size), other ≠ index.val →
      children[other] = some (outcomes[other]'(by omega))) :
    children.set! index.val (some outcomes[index]) = outcomes.map some := by
  apply Array.ext (by simp [size])
  intro other leftInside rightInside
  have inside : other < children.size := by simpa using leftInside
  rw [← getElem!_pos (children.set! index.val (some outcomes[index])) other leftInside, Array.getElem_map]
  by_cases equal : index.val = other
  · subst other
    rw [Array.getElem!_set!_self _ _ _ (by omega)]
    rfl
  · rw [Array.getElem!_set!_ne _ _ _ _ equal, getElem!_pos children other inside,
      others other inside (Ne.symm equal)]

/-- Every fully populated result array settles, even when one or more children
failed. Which failure is selected is determined by `settle_completed`. -/
theorem settle_all_completed (outcomes : Array Exit) :
    ∃ outcome, settle (outcomes.map some) = .completed outcome := by
  rw [settle_completed]
  split <;> exact ⟨_, rfl⟩

end LeanCloud.Result
