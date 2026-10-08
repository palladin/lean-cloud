import LeanCloud.SequentialReplay
import LeanCloud.Proofs.ReplayModel

namespace LeanCloud.Proofs.SequentialExecution
open ReplayModel

abbrev Action := Nat → ExceptT CloudError M Progress
abbrev Step := Assignment → Action

/-- A finite segment has this result for every sufficiently large budget. -/
def Returns (action : Action) (before : Journal) (progress : Progress) (after : Journal) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel → (action fuel).run before = (.ok progress, after)

mutual
  /-- A finite tree of actual replay steps. Fork children finish before the join. -/
  inductive Execution (step : Step) : Location → Action → Journal → Journal → Prop where
    | done (returned : Returns action before .done after) : Execution step branch action before after
    | fork (returned : Returns action before (.fork location count) forked)
        (children : Batch step ((List.range count).map fun index =>
          Assignment.mk 0 (location.child index)) forked joined)
        (resumed : Execution step branch (step ⟨0, branch⟩) joined after) :
        Execution step branch action before after
  inductive Batch (step : Step) : List Assignment → Journal → Journal → Prop where
    | nil : Batch step [] journal journal
    | cons (first : Execution step assignment.branchStart (step assignment) before middle)
        (rest : Batch step assignments middle after) : Batch step (assignment :: assignments) before after
end

/-- Replace the first segment by one with the same eventual result. This also
covers replaying a prefix or recording an effect before the segment starts. -/
theorem Execution.replace {step branch action replacement before middle after}
    (execution : Execution step branch action middle after)
    (same : ∃ offset minimum, ∀ fuel, minimum ≤ fuel →
      (replacement (offset + fuel)).run before = (action fuel).run middle) :
    Execution step branch replacement before after := by
  obtain ⟨offset, minimum, same⟩ := same
  have transfer : ∀ progress journal, Returns action middle progress journal → Returns replacement before progress journal := by
    rintro progress journal ⟨bound, enough⟩
    refine ⟨offset + (bound + minimum), fun fuel large => ?_⟩
    obtain ⟨spare, rfl⟩ := Nat.exists_eq_add_of_le large
    rw [Nat.add_assoc, same _ (by omega)]
    exact enough _ (by omega)
  cases execution with
  | done returned => exact .done (transfer _ _ returned)
  | fork returned children resumed => exact .fork (transfer _ _ returned) children resumed

variable [Codec α] (blobs : BlobStorage M) (program : ι → Cloud M α) (input : ι)

abbrev steps : Step := fun assignment fuel => ReplayInterpreter.step store blobs fuel program input assignment

def finish (fuel : Nat) (branch : Location) (action : Action) : ExceptT CloudError M Unit := do
  let progress ← action fuel
  SequentialReplay.follow (SequentialReplay.run store blobs (program input) (fuel - 1)) branch progress

theorem Execution.runs {branch action before after}
      (execution : Execution (steps blobs program input) branch action before after) :
      ∃ bound, ∀ fuel, bound ≤ fuel → (finish blobs program input fuel branch action).run before = (.ok (), after) := by
    induction execution using Execution.rec
      (motive_2 := fun assignments before after _ =>
        ∃ bound, ∀ fuel, bound ≤ fuel →
          ((assignments.forM (SequentialReplay.run store blobs (program input) fuel)).run before) = (.ok (), after)) with
    | done returned =>
      obtain ⟨bound, returned⟩ := returned
      refine ⟨bound, fun fuel enough => ?_⟩
      simp only [finish, bind_run, returned fuel enough, SequentialReplay.follow, pure_run]
    | fork returned children resumed middle last =>
      obtain ⟨a, first⟩ := returned
      obtain ⟨b, middle⟩ := middle
      obtain ⟨c, last⟩ := last
      refine ⟨max a (max b c + 2), fun fuel enough => ?_⟩
      have positive : 0 < fuel - 1 := by omega
      obtain ⟨n, eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      simp only [finish, bind_run, first fuel (by omega), SequentialReplay.follow]
      have batches := middle (fuel - 1) (by omega)
      simp only [List.forM_eq_forM, List.forM_map] at batches
      simp only [List.forM_eq_forM]
      rw [batches]
      have completed := last (fuel - 1) (by omega)
      simpa only [finish, steps, eq, Nat.add_sub_cancel, Nat.succ_sub_one, SequentialReplay.run, ReplayInterpreter.step] using completed
    | nil => exact ⟨0, by intros; rfl⟩
    | cons first rest firstRuns restRuns =>
      obtain ⟨a, first⟩ := firstRuns
      obtain ⟨b, rest⟩ := restRuns
      refine ⟨max a b + 1, fun fuel enough => ?_⟩
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
      simp only [List.forM]
      rw [bind_run]
      have completed := first (n + 1) (by omega)
      change (SequentialReplay.run store blobs (program input) (n + 1) _).run _ = _ at completed
      rw [completed]
      exact rest (n + 1) (by omega)

end LeanCloud.Proofs.SequentialExecution
