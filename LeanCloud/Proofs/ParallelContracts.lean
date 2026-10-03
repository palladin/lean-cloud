import LeanCloud.Proofs.ReplayContracts
import LeanCloud.Proofs.Recording

/-! The actual replay join reads a stable set of child returns, even when every
read and observation is interrupted. The reduction remains in source order. -/

namespace LeanCloud.Proofs.ParallelContracts
open Lean LeanEff SimulationBackend ReplayModel ReplayInterpreter SimulationLogic

def Children (location : Location) (count : Nat) (outcomes : Nat → Exit) (world : World) : Prop :=
  ∀ index, index < count → world.records.lookup (ReplayStore.returnKey (location.child index)) =
    some ⟨ReplayStore.returnRequest, outcomes index⟩

/-- Keep the caller's stable precondition while gathering every child. A child
failure is an Exit value here; all child records are still read in order. -/
theorem join_preserving (expected : Journal) (worker : WorkerId) (location : Location)
    (count : Nat) (outcomes : Nat → Exit) (pre : World → Prop)
    (stable : (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference pre)
    (completed : ∀ world, (ReplayContracts.rules expected).invariant world → pre world →
      Children location count outcomes world) :
    (ReplayContracts.rules expected).Returns pre
      (Internal.join (observed worker).records location count) (collect ((Array.range count).map outcomes)) := by
  apply Rules.returns_bind (value := (Array.range count).map outcomes)
  · apply Rules.returns_mapM
    intro index member
    apply Rules.returns_bind (value := some (outcomes index))
    · exact ReplayContracts.outcome_preserving expected worker (location.child index) (outcomes index) pre stable
        (fun world invariant holds => completed world invariant holds index (Array.mem_range.mp member))
    · exact Rules.returns_pure _ pre _
  · exact Rules.returns_pure _ pre _

/-- The scheduler's existing JoinReady certificate supplies the same children
as the pure group specification. The invariant rules out incompatible records. -/
theorem join_ready (expected : Journal) (worker : WorkerId) (location : Location)
    (schema : String) (count : Nat) (outcome : Exit) (outcomes : Nat → Exit)
    (group : expected.lookup (ReplayStore.valueKey location) =
      some ⟨⟨"parallel", s!"array({schema})/v1", toJson count⟩, outcome⟩)
    (children : ∀ index, index < count → expected.lookup (ReplayStore.returnKey (location.child index)) =
      some ⟨ReplayStore.returnRequest, outcomes index⟩)
    (collected : collect ((Array.range count).map outcomes) = outcome) :
    (ReplayContracts.rules expected).Returns
      (fun world => Recording.JoinReady expected world.records location)
      (Internal.join (observed worker).records location count) outcome := by
  rw [← collected]
  apply join_preserving
  · exact fun _ _ _ _ grows ready => ready.extend grows
  · intro world invariant ready index inside
    obtain ⟨actual, present, _⟩ := ready schema count outcome group
    have found := present index inside
    have same := Option.some.inj ((invariant _ _ found).symm.trans (children index inside))
    exact found.trans (congrArg some same)

end LeanCloud.Proofs.ParallelContracts
