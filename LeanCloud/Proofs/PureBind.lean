import LeanEff.Core

/-! Replay's structural arguments need only left identity for a pure bind.
The freer continuation syntax does not satisfy all monad laws as syntactic
equalities, so those stronger laws are deliberately not assumed. -/

namespace LeanCloud.Proofs
universe u

class PureBindLaw (m : Type → Type u) [Monad m] : Prop where
  pure_bind : ∀ {α β} (value : α) (next : α → m β), (pure value >>= next) = next value

instance {e : Type → Type u} : PureBindLaw (LeanEff.EffF e) := ⟨fun _ _ => rfl⟩

instance [Monad m] [PureBindLaw m] : PureBindLaw (ExceptT ε m) where
  pure_bind value next := by
    change (pure (Except.ok value) >>= ExceptT.bindCont next) = _
    rw [PureBindLaw.pure_bind]
    rfl

instance [Monad m] [PureBindLaw m] : PureBindLaw (StateT σ m) where
  pure_bind value next := by
    funext state
    change (pure (value, state) >>= _) = _
    rw [PureBindLaw.pure_bind]

end LeanCloud.Proofs
