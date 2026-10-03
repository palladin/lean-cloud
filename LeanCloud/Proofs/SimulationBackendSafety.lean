import LeanCloud.Proofs.SimulationSafety
import LeanCloud.Proofs.SchedulerOwnership

/-! The actual backend adds broker disconnect handling and network events to
the core simulator. This shared proof lifts any compatible semantic system
through those events, without duplicating the simulator's transition cases. -/

namespace LeanCloud.Proofs.SimulationSafety.System
open LeanCloud.SimulationBackend

variable {α : Type} {count : Nat} (system : SimulationSafety.System World count)

theorem backend_step_preserves (start : Simulation.Start World α count)
    (post : Fin count → α → World → Prop)
    (postStable : ∀ actor value, (system.rules actor).Stable (system.rely actor) (post actor value))
    (starts : ∀ actor generation, (system.rules actor).Program (fun _ => True) (post actor) (start actor generation))
    (disconnects : ∀ state actor generation, system.Valid post state →
      system.Valid post { state with world := SimulationBackend.disconnect actor generation state.world } ∧
        system.evolution state.world (SimulationBackend.disconnect actor generation state.world))
    (state after : Simulation.State World α count) (event : Simulation.Event count)
    (valid : system.Valid post state) (executed : SimulationBackend.step start event state = .ok after) :
    system.Valid post after ∧ system.evolution state.world after.world := by
  unfold SimulationBackend.step at executed
  cases result : Simulation.step start event state with
  | error error =>
    rw [result] at executed
    change Except.error error = Except.ok after at executed
    cases executed
  | ok next =>
    obtain ⟨safe, advanced⟩ := system.step_preserves start post postStable starts state next event valid result
    rw [result] at executed
    cases event <;> change Except.ok _ = Except.ok after at executed <;> cases executed
    all_goals first
      | exact ⟨safe, advanced⟩
      | exact let ⟨safe, disconnected⟩ := disconnects _ _ _ safe
        ⟨safe, system.transitive advanced disconnected⟩

theorem backend_trace_preserves (start : Simulation.Start World α count)
    (post : Fin count → α → World → Prop)
    (postStable : ∀ actor value, (system.rules actor).Stable (system.rely actor) (post actor value))
    (starts : ∀ actor generation, (system.rules actor).Program (fun _ => True) (post actor) (start actor generation))
    (disconnects : ∀ state actor generation, system.Valid post state →
      system.Valid post { state with world := SimulationBackend.disconnect actor generation state.world } ∧
        system.evolution state.world (SimulationBackend.disconnect actor generation state.world))
    (network : ∀ state event, system.Valid post state →
      system.Valid post { state with world := networkStep event state.world } ∧
        system.evolution state.world (networkStep event state.world))
    {allowed : Simulation.Event count → Prop} {before after : Simulation.State World α count}
    (valid : system.Valid post before) (history : SchedulerOwnership.Trace start allowed before after) :
    system.Valid post after ∧ system.evolution before.world after.world := by
  induction history with
  | refl => exact ⟨valid, system.reflexive _⟩
  | actor history event admissible executed ih =>
    obtain ⟨safe, advanced⟩ := system.backend_step_preserves start post postStable starts disconnects _ _ event ih.1 executed
    exact ⟨safe, system.transitive ih.2 advanced⟩
  | network history event ih =>
    obtain ⟨safe, advanced⟩ := network _ event ih.1
    exact ⟨safe, system.transitive ih.2 advanced⟩

end LeanCloud.Proofs.SimulationSafety.System
