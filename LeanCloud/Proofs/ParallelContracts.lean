import LeanCloud.Proofs.ReplayContracts
import LeanCloud.Proofs.Recording

/-! Joins inspect immutable child returns. Incomplete groups suspend; complete
ones return the source-ordered result, under arbitrary operation interleaving. -/
namespace LeanCloud.Proofs.ParallelContracts
open Lean LeanEff SimulationBackend ReplayModel ReplayInterpreter SimulationLogic

def Partial (value : α) : Except CloudError (Option α) → World → Prop
  | .error _, _ => False
  | .ok none, _ => True
  | .ok (some actual), _ => actual = value

private theorem readChildren_partial (expected : Journal) (worker : WorkerId) (location : Location)
    (indices : List Nat) (outcomes : Nat → Exit)
    (known : ∀ index ∈ indices, expected.lookup (ReplayStore.returnKey (location.child index)) =
      some ⟨ReplayStore.returnRequest, outcomes index⟩) :
    (ReplayContracts.rules expected).Program (fun _ => True) (Partial (indices.map outcomes))
      (Internal.readChildren (observed worker).records location indices).run := by
  induction indices with
  | nil => exact fun _ _ _ => rfl
  | cons index rest ih =>
    apply Rules.except_bind (middle := fun reply world => Partial (outcomes index) (.ok reply) world)
    · apply Rules.Program.weaken_post _ _ (ReplayContracts.outcome expected worker _ _ (known index (by simp)))
      intro result world invariant holds
      cases result with
      | error _ => exact holds.elim
      | ok reply => cases reply with
        | none => trivial
        | some value => exact holds.1
    · intro reply
      cases reply with
      | none => exact fun _ _ _ => trivial
      | some value =>
        apply Rules.Program.weaken (required := fun _ => value = outcomes index ∧ True)
        · apply Rules.Program.assuming
          intro same
          subst value
          apply Rules.except_bind (middle := fun tail world => Partial (rest.map outcomes) (.ok tail) world)
          · apply Rules.Program.weaken_post _ _ (ih (fun i member => known i (by simp [member])))
            intro result world invariant holds
            cases result <;> exact holds
          · intro tail
            cases tail with
            | none => exact fun _ _ _ => trivial
            | some values => exact fun _ _ holds => congrArg (outcomes index :: ·) holds
        · exact fun _ _ holds => ⟨holds, trivial⟩

/-- A partial read can only produce the specified ordered result. Missing
children are ordinary suspension, never a protocol error. -/
theorem join_partial (expected : Journal) (worker : WorkerId) (location : Location)
    (count : Nat) (outcomes : Nat → Exit)
    (known : ∀ index, index < count → expected.lookup (ReplayStore.returnKey (location.child index)) =
      some ⟨ReplayStore.returnRequest, outcomes index⟩) :
    (ReplayContracts.rules expected).Program (fun _ => True)
      (Partial (collect ((Array.range count).map outcomes)))
      (Internal.tryJoin (observed worker).records location count).run := by
  apply Rules.except_bind (middle := fun values world => Partial ((List.range count).map outcomes) (.ok values) world)
  · apply Rules.Program.weaken_post _ _ (readChildren_partial expected worker location (List.range count) outcomes
      (fun i member => known i (List.mem_range.mp member)))
    intro result world invariant holds
    cases result <;> exact holds
  · intro values
    cases values with
    | none => exact fun _ _ _ => trivial
    | some values =>
      intro world invariant holds
      have ordered : ((List.range count).map outcomes).toArray = (Array.range count).map outcomes := by
        apply Array.toList_inj.mp
        simp
      change values = (List.range count).map outcomes at holds
      simp only [Partial, Option.map_some, holds, ordered]

private theorem readChildren_preserving (expected : Journal) (worker : WorkerId) (location : Location)
    (indices : List Nat) (outcomes : Nat → Exit) (pre : World → Prop)
    (stable : (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference pre)
    (completed : ∀ world, (ReplayContracts.rules expected).invariant world → pre world →
      ∀ index ∈ indices, world.records.lookup (ReplayStore.returnKey (location.child index)) =
        some ⟨ReplayStore.returnRequest, outcomes index⟩) :
    (ReplayContracts.rules expected).Returns pre
      (Internal.readChildren (observed worker).records location indices) (some (indices.map outcomes)) := by
  induction indices with
  | nil => exact Rules.returns_pure _ pre _
  | cons index rest ih =>
    apply Rules.except_bind_value _ _ _ (some (outcomes index))
      (ReplayContracts.outcome_preserving expected worker _ _ pre stable
        (fun world invariant holds => completed world invariant holds index (by simp)))
    apply Rules.except_bind_value _ _ _ (some (rest.map outcomes))
      (ih (fun world invariant holds i member => completed world invariant holds i (by simp [member])))
    exact Rules.returns_pure _ pre _

theorem join_preserving (expected : Journal) (worker : WorkerId) (location : Location)
    (count : Nat) (outcomes : Nat → Exit) (pre : World → Prop)
    (stable : (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference pre)
    (completed : ∀ world, (ReplayContracts.rules expected).invariant world → pre world →
      ∀ index, index < count → world.records.lookup (ReplayStore.returnKey (location.child index)) =
        some ⟨ReplayStore.returnRequest, outcomes index⟩) :
    (ReplayContracts.rules expected).Returns pre
      (Internal.tryJoin (observed worker).records location count) (some (collect ((Array.range count).map outcomes))) := by
  apply Rules.except_bind_value _ _ _ (some ((List.range count).map outcomes))
    (readChildren_preserving expected worker location (List.range count) outcomes pre stable
      (fun world invariant holds i member => completed world invariant holds i (List.mem_range.mp member)))
  have ordered : ((List.range count).map outcomes).toArray = (Array.range count).map outcomes := by
    apply Array.toList_inj.mp
    simp
  simp only [Option.map_some, ordered]
  exact fun _ _ holds => ⟨rfl, holds⟩

/-- A scheduler checkpoint whose children are complete cannot suspend again. -/
theorem join_ready (expected : Journal) (worker : WorkerId) (location : Location)
    (schema : String) (count : Nat) (outcome : Exit) (outcomes : Nat → Exit)
    (group : expected.lookup (ReplayStore.valueKey location) =
      some ⟨⟨"parallel", s!"array({schema})/v1", toJson count⟩, outcome⟩)
    (children : ∀ index, index < count → expected.lookup (ReplayStore.returnKey (location.child index)) =
      some ⟨ReplayStore.returnRequest, outcomes index⟩)
    (collected : collect ((Array.range count).map outcomes) = outcome) :
    (ReplayContracts.rules expected).Returns
      (fun world => Recording.JoinReady expected world.records location)
      (Internal.tryJoin (observed worker).records location count) (some outcome) := by
  rw [← collected]
  apply join_preserving
  · exact fun _ _ _ _ grows ready => ready.extend grows
  · intro world invariant ready index inside
    obtain ⟨actual, present, _⟩ := ready schema count outcome group
    have found := present index inside
    have same := Option.some.inj ((invariant _ _ found).symm.trans (children index inside))
    exact found.trans (congrArg some same)

end LeanCloud.Proofs.ParallelContracts
