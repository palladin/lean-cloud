import LeanCloud.Proofs.Parallel
import LeanCloud.Proofs.Assumptions

/-! Encoding completed child outcomes preserves array order and selects the
same values or error as direct evaluation, regardless of completion order. -/

namespace LeanCloud.Proofs
open Lean

/-- The persistent representation of a typed child outcome. -/
def encodeOutcome (codec : Codec α) : Except CloudError α → Exit
  | .ok value => .success (codec.encode value)
  | .error error => .failure error

private theorem collect_list_length (outcomes : List (Except CloudError α)) (values : List α)
    (collected : outcomes.mapM id = .ok values) : values.length = outcomes.length := by
  induction outcomes generalizing values with
  | nil => change Except.ok [] = Except.ok values at collected; cases collected; rfl
  | cons head tail ih =>
    cases head with
    | error error => simp [List.mapM_cons, bind, Except.bind] at collected
    | ok value =>
      simp only [List.mapM_cons] at collected
      cases selected : tail.mapM id with
      | error error => simp [selected, bind, Except.bind] at collected
      | ok rest =>
        simp [selected, bind, Except.bind, pure, Except.pure] at collected
        subst values
        simp [ih rest selected]

theorem collect_outcomes_size (outcomes : Array (Except CloudError α)) (values : Array α)
    (collected : outcomes.mapM id = .ok values) : values.size = outcomes.size := by
  simp only [Array.mapM_eq_mapM_toList] at collected
  cases selected : outcomes.toList.mapM id with
  | error error => simp [selected, Functor.map, Except.map] at collected
  | ok rest =>
    simp [selected, Functor.map, Except.map] at collected
    subst values
    simpa using collect_list_length outcomes.toList rest selected

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

end LeanCloud.Proofs
