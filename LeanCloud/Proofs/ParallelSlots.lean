import LeanCloud.Proofs.Parallel
import LeanCloud.Proofs.Assumptions

/-! Encoding an ordered prefix of child outcomes into the runtime's partial
result array. The first missing slot determines the next child; a full array
selects the same values or error as direct evaluation. -/

namespace LeanCloud.Proofs
open Lean

/-- The persistent representation of a typed child outcome. -/
def encodeOutcome (codec : Codec α) : Except CloudError α → Exit
  | .ok value => .success (codec.encode value)
  | .error error => .failure error

private theorem collect_encoded_list (codec : Codec α) (outcomes : List (Except CloudError α)) :
    outcomes.mapM (fun outcome => match encodeOutcome codec outcome with
      | .success value => Except.ok value
      | outcome => Except.error outcome) =
    match outcomes.mapM id with
    | .ok values => Except.ok (values.map codec.encode)
    | .error error => Except.error (.failure error) := by
  induction outcomes with
  | nil => rfl
  | cons outcome rest ih =>
    cases outcome with
    | error error => simp [List.mapM_cons, encodeOutcome]; rfl
    | ok value =>
      simp only [List.mapM_cons, ih]
      cases collected : rest.mapM id <;> rfl

/-- Encoding child outcomes commutes with selecting the group's result. Both
representations choose the first error in array order. -/
theorem settle_encoded (codec : Codec α) (outcomes : Array (Except CloudError α)) :
    Result.settle ((outcomes.map (encodeOutcome codec)).map some) =
      .completed (match outcomes.mapM id with
        | .ok values => .success (Json.arr (values.map codec.encode))
        | .error error => .failure error) := by
  rw [Result.settle_completed]
  simp only [Array.mapM_eq_mapM_toList, Array.toList_map, List.mapM_map, Function.comp_def]
  have collected := collect_encoded_list codec outcomes.toList
  simp only [encodeOutcome] at collected ⊢
  erw [collected]
  cases collected : outcomes.toList.mapM id <;> simp [Functor.map, Except.map]

/-- The runtime's partial array after an ordered prefix of children finished. -/
def parallelSlots (codec : Codec α) (count : Nat) (outcomes : Array (Except CloudError α)) :
    Array (Option Exit) :=
  outcomes.map (fun outcome => some (encodeOutcome codec outcome)) ++
    Array.replicate (count - outcomes.size) none

@[simp] theorem parallelSlots_empty (codec : Codec α) (count : Nat) :
    parallelSlots codec count #[] = Array.replicate count none := by
  simp [parallelSlots]

theorem parallelSlots_size (codec : Codec α) (count : Nat)
    (outcomes : Array (Except CloudError α)) (bound : outcomes.size ≤ count) :
    (parallelSlots codec count outcomes).size = count := by
  simp only [parallelSlots, Array.size_append, Array.size_map, Array.size_replicate]
  omega

theorem parallelSlots_full (codec : Codec α) (outcomes : Array (Except CloudError α)) :
    parallelSlots codec outcomes.size outcomes = (outcomes.map (encodeOutcome codec)).map some := by
  simp [parallelSlots, Array.map_map, Function.comp_def]

theorem parallelSlots_get_finished (codec : Codec α) (count : Nat)
    (outcomes : Array (Except CloudError α)) (index : Nat) (inside : index < outcomes.size) :
    (parallelSlots codec count outcomes)[index]! = some (encodeOutcome codec outcomes[index]) := by
  have valid : index < (parallelSlots codec count outcomes).size := by
    simp only [parallelSlots, Array.size_append, Array.size_map, Array.size_replicate]
    omega
  rw [getElem!_pos (parallelSlots codec count outcomes) index valid]
  simp [parallelSlots, inside]

theorem parallelSlots_get_pending (codec : Codec α) (count : Nat)
    (outcomes : Array (Except CloudError α)) (index : Nat)
    (pending : outcomes.size ≤ index) (inside : index < count) :
    (parallelSlots codec count outcomes)[index]! = none := by
  have size := parallelSlots_size codec count outcomes (by omega)
  rw [getElem!_pos (parallelSlots codec count outcomes) index (by omega)]
  simp [parallelSlots, Array.getElem_append, Nat.not_lt_of_ge pending]

/-- The actual driver selects precisely the next child after the executed prefix. -/
theorem parallelSlots_select (codec : Codec α) (count : Nat)
    (outcomes : Array (Except CloudError α)) (inside : outcomes.size < count) :
    (parallelSlots codec count outcomes).findIdx? Option.isNone = some outcomes.size := by
  apply Array.findIdx?_eq_some_iff_getElem.mpr
  have size := parallelSlots_size codec count outcomes (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · have empty := parallelSlots_get_pending codec count outcomes outcomes.size (by omega) inside
    rw [getElem!_pos _ _ (by omega)] at empty
    simp [empty]
  · intro index earlier
    have filled := parallelSlots_get_finished codec count outcomes index earlier
    rw [getElem!_pos _ _ (by omega)] at filled
    simp [filled]

/-- Filling the next slot extends exactly the ordered prefix. -/
theorem parallelSlots_update (codec : Codec α) (count : Nat)
    (outcomes : Array (Except CloudError α)) (inside : outcomes.size < count)
    (outcome : Except CloudError α) :
    (parallelSlots codec count outcomes).set! outcomes.size (some (encodeOutcome codec outcome)) =
      parallelSlots codec count (outcomes.push outcome) := by
  have oldSize := parallelSlots_size codec count outcomes (by omega)
  have newSize := parallelSlots_size codec count (outcomes.push outcome) (by simp; omega)
  apply Array.ext (by simp [oldSize, newSize])
  intro index leftInside rightInside
  have valid : index < count := by simpa only [Array.size_set!, oldSize] using leftInside
  rw [← getElem!_pos ((parallelSlots codec count outcomes).set! outcomes.size
    (some (encodeOutcome codec outcome))) index leftInside,
    ← getElem!_pos (parallelSlots codec count (outcomes.push outcome)) index rightInside]
  by_cases same : outcomes.size = index
  · subst index
    rw [Array.getElem!_set!_self _ _ _ (by omega),
      parallelSlots_get_finished codec count (outcomes.push outcome) outcomes.size (by simp)]
    simp
  · rw [Array.getElem!_set!_ne _ _ _ _ same]
    by_cases earlier : index < outcomes.size
    · rw [parallelSlots_get_finished codec count outcomes index earlier,
        parallelSlots_get_finished codec count (outcomes.push outcome) index (by simp; omega)]
      simp [Array.getElem_push_lt, earlier]
    · rw [parallelSlots_get_pending codec count outcomes index (by omega) valid,
        parallelSlots_get_pending codec count (outcomes.push outcome) index (by simp; omega) valid]

theorem parallelSlots_waits (codec : Codec α) (count : Nat)
    (outcomes : Array (Except CloudError α)) (inside : outcomes.size < count) :
    Result.settle (parallelSlots codec count outcomes) = .suspended (parallelSlots codec count outcomes) := by
  apply Result.settle_missing
  have size := parallelSlots_size codec count outcomes (by omega)
  have missing := parallelSlots_get_pending codec count outcomes outcomes.size (by omega) inside
  rw [getElem!_pos (parallelSlots codec count outcomes) outcomes.size (by omega)] at missing
  exact Array.mem_of_getElem missing

end LeanCloud.Proofs
