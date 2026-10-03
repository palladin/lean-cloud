import LeanCloud.Proofs.ReplayContracts
import LeanCloud.Proofs.Recording

/-! The actual replay join reads a stable set of child returns, even when every
read and observation is interrupted. The reduction remains in source order. -/

namespace LeanCloud.Proofs.ParallelContracts
open Lean LeanEff SimulationBackend ReplayModel ReplayInterpreter SimulationLogic

def Children (location : Location) (count : Nat) (outcomes : Nat → Exit) (world : World) : Prop :=
  ∀ index, index < count → world.records.lookup (ReplayStore.returnKey (location.child index)) =
    some ⟨ReplayStore.returnRequest, outcomes index⟩

theorem children_stable (expected : Journal) (location : Location) (count : Nat) (outcomes : Nat → Exit) :
    (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference
      (Children location count outcomes) := by
  intro before after _ _ grows completed index inside
  exact grows _ _ (completed index inside)

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

theorem join (expected : Journal) (worker : WorkerId) (location : Location)
    (count : Nat) (outcomes : Nat → Exit) :
    (ReplayContracts.rules expected).Returns (Children location count outcomes)
      (Internal.join (observed worker).records location count) (collect ((Array.range count).map outcomes)) :=
  join_preserving expected worker location count outcomes _ (children_stable expected location count outcomes)
    (fun _ _ completed => completed)

/-- The concurrent join has the same ordered reduction used by the direct
interpreter. Completion order cannot reorder values or select another error. -/
theorem join_matches_ordered_outcomes (expected : Journal) (worker : WorkerId) (location : Location)
    (count : Nat) (outcomes : Nat → Except CloudError α) (encode : α → Json) :
    (ReplayContracts.rules expected).Returns
      (Children location count (fun index => Parallel.recorded encode (outcomes index)))
      (Internal.join (observed worker).records location count)
      (Parallel.recorded (fun values => Json.arr (values.map encode)) (((Array.range count).map outcomes).mapM id)) := by
  have ordered := Parallel.collect_matches_direct ((Array.range count).map outcomes) encode
  simp only [Array.map_map, Function.comp_def] at ordered
  rw [← ordered]
  exact join expected worker location count _

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

/-- This is the join-and-record fragment of the actual replay walk. The value
is correct and durable before the continuation can decode it. Competing writes
are allowed; the expected journal fixes their common result. -/
theorem record_join (expected : Journal) (worker : WorkerId) (location : Location)
    (schema : String) (count : Nat) (outcome : Exit) (outcomes : Nat → Exit)
    (group : expected.lookup (ReplayStore.valueKey location) =
      some ⟨⟨"parallel", s!"array({schema})/v1", toJson count⟩, outcome⟩)
    (children : ∀ index, index < count → expected.lookup (ReplayStore.returnKey (location.child index)) =
      some ⟨ReplayStore.returnRequest, outcomes index⟩)
    (collected : collect ((Array.range count).map outcomes) = outcome) :
    let request : Request := ⟨"parallel", s!"array({schema})/v1", toJson count⟩
    (ReplayContracts.rules expected).Program (fun world => Recording.JoinReady expected world.records location)
      (fun result world => result = Except.ok outcome ∧
        Recording.JoinReady expected world.records location ∧
        world.records.lookup (ReplayStore.valueKey location) = some ⟨request, outcome⟩)
      ((do
        let joined ← Internal.join (observed worker).records location count
        let accepted ← (observed worker).records.create (ReplayStore.valueKey location) ⟨request, joined⟩
        Internal.check request accepted : ExceptT CloudError (SimM World) Exit).run) := by
  dsimp only
  apply Rules.except_bind_value _ _ _ outcome (join_ready expected worker location schema count outcome outcomes group children collected)
  exact ReplayContracts.create_checked expected worker _ _ group _
    (fun _ _ _ _ grows ready => ready.extend grows)

end LeanCloud.Proofs.ParallelContracts
