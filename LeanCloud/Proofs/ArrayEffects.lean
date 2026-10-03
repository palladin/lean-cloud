module

public import Init.Data.Array.Lemmas
public import Init.Data.Array.Extract
import all Init.Data.Array.Basic
import all Init.Data.Fin.Fold
public import Init.Data.Array.OfFn
import all Init.Data.Array.OfFn
import Init.Omega

public section
namespace LeanCloud.Proofs

/-- Pure array construction only needs the pure cases of map and bind, not
associativity for arbitrary computations. This also applies to lean-eff. -/
theorem array_ofFnM_pure {m : Type → Type u} [Monad m]
    (pureBind : ∀ {α β : Type} (value : α) (next : α → m β), (pure value >>= next) = next value)
    (pureMap : ∀ {α β : Type} (f : α → β) (value : α), f <$> (pure value : m α) = pure (f value))
    (values : Fin count → α) :
    Array.ofFnM (fun index => (pure (values index) : m α)) = pure (Array.ofFn values) := by
  simp only [Array.ofFnM, pureMap]
  exact (loop (Array.emptyWithCapacity count) 0).trans (congrArg pure Array.idRun_ofFnM)
where
  loop (acc : Array α) (index : Nat) :
      Fin.foldlM.loop (m := m) count (fun acc index => pure (acc.push (values index))) acc index =
        pure (Fin.foldlM.loop (m := Id) count (fun acc index => pure (acc.push (values index))) acc index) := by
    rw [Fin.foldlM.loop, Fin.foldlM.loop]
    split
    next inside =>
      rw [pureBind]
      exact loop (acc.push (values ⟨index, inside⟩)) (index + 1)
    next outside => rfl
  termination_by count - index

/-- Array traversal preserves any property closed under pure and bind. This
uses the actual array loop and needs no syntactic monad laws from lean-eff. -/
theorem array_mapM_preserves {m : Type → Type u} [Monad m]
    (property : {α : Type} → m α → Prop)
    (pureValid : ∀ {α : Type} (value : α), property (pure value))
    (bindValid : ∀ {α β : Type} (first : m α) (next : α → m β),
      property first → (∀ value, property (next value)) → property (first >>= next))
    (items : Array α) (body : α → m β) (valid : ∀ item, property (body item)) :
    property (items.mapM body) := loop 0 _
where
  loop (index : Nat) (acc : Array β) : property (Array.mapM.map body items index acc) := by
    rw [Array.mapM.map]
    split
    · apply bindValid _ _ (valid _)
      intro value
      exact loop (index + 1) (acc.push value)
    · exact pureValid _
  termination_by items.size - index

/-- The actual array loop returns results in source order. The supplied
sequencing rule can describe semantic contracts without monad equalities. -/
theorem array_mapM_returns {m : Type → Type u} [Monad m]
    (returns : {α : Type} → m α → α → Prop)
    (pureValid : ∀ {α : Type} (value : α), returns (pure value) value)
    (bindValid : ∀ {α β : Type} (first : m α) (next : α → m β) (value : α) (result : β),
      returns first value → returns (next value) result → returns (first >>= next) result)
    (items : Array α) (body : α → m β) (expected : α → β)
    (valid : ∀ item ∈ items, returns (body item) (expected item)) :
    returns (items.mapM body) (items.map expected) :=
  loop 0 #[] (Nat.zero_le _) (by simp)
where
  loop (index : Nat) (acc : Array β) (bound : index ≤ items.size)
      (collected : acc = (items.extract 0 index).map expected) :
      returns (Array.mapM.map body items index acc) (items.map expected) := by
    rw [Array.mapM.map]
    split
    next inside =>
      apply bindValid _ _ (expected items[index]) _ (valid _ (Array.getElem_mem inside))
      apply loop (index + 1) (acc.push (expected items[index])) (by omega)
      rw [collected, Array.extract_succ_right (by omega) inside, Array.map_push]
    next outside =>
      have last : index = items.size := by omega
      subst index
      simp only [Array.extract_size] at collected
      subst acc
      exact pureValid _
  termination_by items.size - index

end LeanCloud.Proofs
