import Init.Data.Array.Lemmas

namespace LeanCloud.Proofs.OptionalResults

theorem mapM_present {items : List α} {f : α → Option β} {values : List β}
    (complete : items.mapM f = some values) : ∀ item ∈ items, (f item).isSome = true := by
  induction items generalizing values with
  | nil => simp
  | cons item rest ih =>
    cases first : f item with
    | none => simp [List.mapM_cons, first] at complete
    | some value =>
      cases found : rest.mapM f with
      | none => simp [List.mapM_cons, first, found] at complete
      | some tail =>
        intro other member
        rcases List.mem_cons.mp member with rfl | member
        · simp [first]
        · exact ih found other member

end LeanCloud.Proofs.OptionalResults
