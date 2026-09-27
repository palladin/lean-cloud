import LeanCloud.Proofs.ReplayExecution
import LeanCloud.Proofs.Transitions
import LeanCloud.Proofs.Freshness

namespace LeanCloud.Proofs.ReplayModel
open Lean ReplayInterpreter.Internal

theorem run_completed [Codec α] (blobs : BlobModel World) (fuel : Nat)
    (root : Cloud (StateM World) Json) (journal : Journal) (pending : List Location)
    (outcome : Exit) (world : World) :
    (run (α := α) (storage blobs) queue (fuel + 1) root).run ⟨journal, pending, some outcome⟩ world =
      ((decodeExit outcome, ⟨journal, pending, some outcome⟩), world) := by
  rw [run]
  exact result_run outcome _ _

/-- A finite segment of actual work-item processing. Its equations describe the
runtime step; no parallel evaluator or alternative replay implementation is used. -/
inductive Segment {World : Type} (blobs : BlobModel World) (root : Cloud (StateM World) Json) :
    State → World → State → World → Prop where
  | refl (state : State) (world : World) : Segment blobs root state world state world
  | one {journal location rest world nextState nextWorld updateResult bound}
      (stepped : ∀ fuel, bound ≤ fuel →
        (step (storage blobs) fuel root location).run ⟨journal, location :: rest, none⟩ world =
          ((.ok updateResult, nextState), nextWorld)) :
      Segment blobs root ⟨journal, location :: rest, none⟩ world
        (update nextState location updateResult) nextWorld
  | trans {first middle last before between after}
      (head : Segment blobs root first before middle between)
      (tail : Segment blobs root middle between last after) :
      Segment blobs root first before last after

/-- Enough fuel executes the whole segment, leaving the remaining fuel to the
same driver at the segment's endpoint. The bound also covers reconstruction. -/
theorem Segment.correct [Codec α] {blobs : BlobModel World} {root : Cloud (StateM World) Json}
    {state finalState : State} {world finalWorld : World}
    (segment : Segment blobs root state world finalState finalWorld) :
    ∃ cost bound, ∀ fuel, bound ≤ fuel → 0 < fuel →
      (run (α := α) (storage blobs) queue (fuel + cost) root).run state world =
        (run (α := α) (storage blobs) queue fuel root).run finalState finalWorld := by
  induction segment with
  | refl state world => exact ⟨0, 0, fun _ _ _ => rfl⟩
  | @one journal location rest world nextState nextWorld updateResult bound stepped =>
    refine ⟨1, bound, ?_⟩
    intro fuel enough positive
    have equation := run_selected (α := α) _ _ fuel _ _ _ _ _ _ _ (stepped (fuel + 1) (by omega))
    cases updateResult with
    | runnable locations => exact equation
    | done outcome =>
      obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      rw [show update nextState location (.done outcome) =
        ⟨nextState.journal, [], some outcome⟩ from rfl, run_completed]
      exact equation
  | trans head tail ihHead ihTail =>
    obtain ⟨headCost, headBound, headCorrect⟩ := ihHead
    obtain ⟨tailCost, tailBound, tailCorrect⟩ := ihTail
    refine ⟨headCost + tailCost, max headBound tailBound, ?_⟩
    intro fuel enough positive
    have first := headCorrect (fuel + tailCost) (by omega) (by omega)
    have last := tailCorrect fuel (by omega) positive
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.trans last

/-- A segment ending in a final environment outcome establishes an actual run,
with a bound that holds for every larger fuel budget. -/
theorem Segment.finished [Codec α] {blobs : BlobModel World} {root : Cloud (StateM World) Json}
    {state : State} {world finalWorld : World} {journal : Journal} {outcome : Exit}
    (segment : Segment blobs root state world ⟨journal, [], some outcome⟩ finalWorld) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      (run (α := α) (storage blobs) queue fuel root).run state world =
        ((decodeExit outcome, ⟨journal, [], some outcome⟩), finalWorld) := by
  obtain ⟨cost, bound, correct⟩ := segment.correct (α := α)
  refine ⟨cost + bound + 1, ?_⟩
  intro fuel enough
  have eq := correct (fuel - cost) (by omega) (by omega)
  have positive : 0 < fuel - cost := by omega
  obtain ⟨remaining, remainingEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  rw [show fuel - cost + cost = fuel by omega, remainingEq, run_completed] at eq
  exact eq

end LeanCloud.Proofs.ReplayModel
