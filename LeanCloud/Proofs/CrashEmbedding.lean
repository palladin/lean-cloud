import LeanCloud.Proofs.BackendMap
import LeanCloud.Proofs.CrashSpec

/-! Embedding a component's operations in a shared durable state. Fault
bookkeeping is shared, and the other component survives both return and crash.
The embedded action keeps its original sequence of primitive operations. -/

namespace LeanCloud.Proofs.CrashRecovery
open CrashModel

def withLeft (action : M δ α) : M (δ × ε) α := fun start =>
  let (result, final) := action.run ⟨start.durable.1, start.faults⟩
  (result, ⟨(final.durable, start.durable.2), final.faults⟩)

def withRight (action : M ε α) : M (δ × ε) α := fun start =>
  let (result, final) := action.run ⟨start.durable.2, start.faults⟩
  (result, ⟨(start.durable.1, final.durable), final.faults⟩)

def leftMap (δ ε : Type) : BackendMap (M δ) (M (δ × ε)) where
  map := withLeft
  map_pure _ := rfl
  map_bind action next := by
    funext start
    simp only [ExceptT.run, withLeft, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, bind, pure]
    cases action ⟨start.durable.1, start.faults⟩ with
    | mk outcome final => cases outcome <;> rfl

def rightMap (δ ε : Type) : BackendMap (M ε) (M (δ × ε)) where
  map := withRight
  map_pure _ := rfl
  map_bind action next := by
    funext start
    simp only [ExceptT.run, withRight, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, bind, pure]
    cases action ⟨start.durable.2, start.faults⟩ with
    | mk outcome final => cases outcome <;> rfl

/-- Frame an arbitrary invariant about the other durable component. -/
theorem Triple.withLeft {action : M δ α} {pre post stopped}
    (spec : Triple pre action post stopped) (frame : ε → Prop) :
    Triple (fun state => pre state.1 ∧ frame state.2) (withLeft action)
      (fun value state => post value state.1 ∧ frame state.2)
      (fun state => stopped state.1 ∧ frame state.2) := by
  intro start valid
  have safe := spec ⟨start.durable.1, start.faults⟩ valid.1
  change let (result, final) := (CrashRecovery.withLeft action).run start; _
  simp only [CrashRecovery.withLeft, ExceptT.run]
  dsimp only [ExceptT.run] at safe
  generalize execution : action ⟨start.durable.1, start.faults⟩ = run at *
  rcases run with ⟨result, final⟩
  refine ⟨safe.1, ?_⟩
  cases result with
  | ok value => exact ⟨safe.2, valid.2⟩
  | error crash => exact ⟨⟨safe.2.1, valid.2⟩, safe.2.2⟩

theorem Triple.withRight {action : M ε α} {pre post stopped}
    (spec : Triple pre action post stopped) (frame : δ → Prop) :
    Triple (fun state => frame state.1 ∧ pre state.2) (withRight action)
      (fun value state => frame state.1 ∧ post value state.2)
      (fun state => frame state.1 ∧ stopped state.2) := by
  intro start valid
  have safe := spec ⟨start.durable.2, start.faults⟩ valid.2
  change let (result, final) := (CrashRecovery.withRight action).run start; _
  simp only [CrashRecovery.withRight, ExceptT.run]
  dsimp only [ExceptT.run] at safe
  generalize execution : action ⟨start.durable.2, start.faults⟩ = run at *
  rcases run with ⟨result, final⟩
  refine ⟨safe.1, ?_⟩
  cases result with
  | ok value => exact ⟨valid.1, safe.2⟩
  | error crash => exact ⟨⟨valid.1, safe.2.1⟩, safe.2.2⟩

end LeanCloud.Proofs.CrashRecovery
