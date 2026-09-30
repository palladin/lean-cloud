import LeanCloud.Result
import Init.Data.Array.Monadic

/-! Laws for the actual parallel-result bookkeeping used by replay.
Repeated child completion requires explicit reflexivity of the outcome's
equality check, because the existing comparator delegates to partial JSON
comparison. -/

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

theorem recordChild_missing (children : Array (Option Exit)) (index : Nat) (outcome : Exit)
    (inside : index < children.size) (missing : children[index]! = none) :
    recordChild (.suspended children) index outcome =
      .ok (settle (children.set! index (some outcome))) := by
  simp [recordChild, Nat.not_le_of_lt inside, missing]
  rfl

theorem recordChild_existing (children : Array (Option Exit)) (index : Nat) (outcome : Exit)
    (inside : index < children.size) (recorded : children[index]! = some outcome)
    (reflexive : (outcome == outcome) = true) :
    recordChild (.suspended children) index outcome = .ok (settle children) := by
  simp [recordChild, Nat.not_le_of_lt inside, recorded, reflexive]
  rfl

theorem settle_suspended {children slots : Array (Option Exit)}
    (settled : settle children = .suspended slots) : children = slots := by
  unfold settle at settled
  split at settled
  · cases settled; rfl
  · split at settled <;> cases settled

/-- A suspended result really has an unfilled position. This is about the
returned array, independently of later publications to the physical journal. -/
theorem settle_suspended_missing {children slots : Array (Option Exit)}
    (settled : settle children = .suspended slots) : none ∈ slots := by
  have same := settle_suspended settled
  subst slots
  classical
  by_cases missing : none ∈ children
  · exact missing
  have collect (values : List (Option Exit)) (filled : none ∉ values) :
      ∃ outcomes, values.mapM id = some outcomes := by
    induction values with
    | nil => exact ⟨[], rfl⟩
    | cons value rest ih =>
      cases value with
      | none => exact False.elim (filled (by simp))
      | some value =>
        obtain ⟨outcomes, collected⟩ := ih (fun present => filled (by simp [present]))
        exact ⟨value :: outcomes, by simp [List.mapM_cons, collected]⟩
  obtain ⟨outcomes, collected⟩ := collect children.toList (by simpa using missing)
  have complete : children.mapM id = some outcomes.toArray := by
    rw [Array.mapM_eq_mapM_toList, collected]
    rfl
  simp only [settle, complete] at settled
  split at settled <;> cases settled

/-- A completed group has an outcome at every array position. -/
theorem settle_filled {children : Array (Option Exit)} {outcome : Exit}
    (settled : settle children = .completed outcome) (index : Nat) (inside : index < children.size) :
    ∃ value, children[index]! = some value := by
  cases slot : children[index]! with
  | some value => exact ⟨value, rfl⟩
  | none =>
    have missing : none ∈ children := by
      have same : children[index] = none := by simpa only [getElem!_pos children index inside] using slot
      rw [← same]
      exact Array.getElem_mem inside
    rw [settle_missing children missing] at settled
    cases settled

end LeanCloud.Result
