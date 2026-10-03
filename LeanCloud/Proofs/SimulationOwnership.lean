import LeanCloud.Proofs.SimulationEvolution

/-! Ownership of a durable field across the actual Sim event machine. Only its
owner's local operations may change it. The shared event proof also checks
remote requests that survive their originating process as orphans. -/

namespace LeanCloud.Proofs.SimulationOwnership
open LeanEff Simulation

variable {δ σ α : Type} (field : δ → σ)

def Allowed (owner : Bool) : Atomic δ β → Prop
  | .step remote _ operation =>
      remote = true ∨ owner = false → ∀ world, field (operation world).2 = field world

abbrev Valid (owner : Fin count) (state : State δ α count) : Prop :=
  SimulationEvolution.Valid (fun actor => Allowed field (actor == owner))
    (fun before after => field after = field before) state

theorem initial (owner : Fin count) (world : δ) (start : Start δ α count)
    (valid : ∀ actor generation, Effects.Program (Allowed field (actor == owner)) (start actor generation)) :
    Valid field owner (State.initial world start) := SimulationEvolution.initial world start valid

/-- Every actual event preserves ownership, including reply suspension, process
restart, and a remote commit after the originating process has died. -/
theorem step_preserves (owner : Fin count) (start : Start δ α count)
    (starts : ∀ actor generation, Effects.Program (Allowed field (actor == owner)) (start actor generation))
    (state after : State δ α count) (event : Event count) (valid : Valid field owner state)
    (executed : Simulation.step start event state = .ok after) :
    Valid field owner after ∧ (event = .commit owner ∨ field after.world = field state.world) := by
  have safe := SimulationEvolution.step_preserves
    (orphanAdvance := fun before after => field after = field before)
    (fun actor before after => actor = owner ∨ field after = field before)
    (fun _ => rfl) start starts
    (by
      intro actor β remote label operation sound world
      by_cases same : actor = owner
      · exact .inl same
      · exact .inr (sound (.inr (by simp [same])) world))
    (by
      intro actor β label operation sound world
      exact sound (.inl rfl) world)
    state after event valid executed
  refine ⟨safe.1, ?_⟩
  rcases safe.2 with ⟨actor, committed, same | preserved⟩ | preserved
  · exact .inl (committed.trans (congrArg Event.commit same))
  · exact .inr preserved
  · exact .inr preserved

end LeanCloud.Proofs.SimulationOwnership
