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

theorem recordChild_missing (children : Array (Option Exit)) (index : Nat) (outcome : Exit)
    (inside : index < children.size) (missing : children[index]! = none) :
    recordChild (.suspended children) index outcome =
      .ok (settle (children.set! index (some outcome))) := by
  simp [recordChild, Nat.not_le_of_lt inside, missing]
  rfl

end LeanCloud.Result
