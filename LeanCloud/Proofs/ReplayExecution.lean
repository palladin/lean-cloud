import LeanCloud.SequentialReplay
import LeanCloud.Proofs.JournalMerge

namespace LeanCloud.Proofs.ReplayExecution
open ReplayModel

inductive Mode where
  | sequential | parallel

abbrev Action := Nat → ExceptT CloudError M Progress
abbrev Step := Assignment → Action

/-- A finite segment has this result for every sufficiently large budget. -/
def Returns (action : Action) (before : Journal) (progress : Progress) (after : Journal) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel → (action fuel).run before = (.ok progress, after)

mutual
  /-- A finite tree of replay steps, independent of runtime actors and delivery. -/
  inductive Execution (step : Step) : Mode → Location → Action → Journal → Journal → Prop where
    | done (returned : Returns action before .done after) : Execution step mode branch action before after
    | fork (returned : Returns action before (.fork location count) forked)
        (children : Batch step mode ((List.range count).map fun index =>
          Assignment.mk 0 (location.child index)) forked joined)
        (resumed : Execution step mode branch (step ⟨0, branch⟩) joined after) :
        Execution step mode branch action before after
  inductive Batch (step : Step) : Mode → List Assignment → Journal → Journal → Prop where
    | nil : Batch step .sequential [] journal journal
    | cons (first : Execution step .sequential assignment.branchStart (step assignment) before middle)
        (rest : Batch step .sequential assignments middle after) :
        Batch step .sequential (assignment :: assignments) before after
    | parallel {κ : Type} (items : List κ) (job : κ → Assignment) (journals : κ → Journal)
        (children : ∀ item ∈ items,
          Execution step .parallel (job item).branchStart (step (job item)) before (journals item))
        (merged : (ParallelReplay.mergeChildren (items.map fun item =>
          (.ok (), newRecords before (journals item)))).run before = (.ok (), after)) :
        Batch step .parallel (items.map job) before after
end

/-- Replace the first segment by one with the same eventual result. This also
covers replaying a prefix or recording an effect before the segment starts. -/
theorem Execution.replace {step mode branch action replacement before middle after}
    (execution : Execution step mode branch action middle after)
    (same : ∃ offset minimum, ∀ fuel, minimum ≤ fuel →
      (replacement (offset + fuel)).run before = (action fuel).run middle) :
    Execution step mode branch replacement before after := by
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

def run (mode : Mode) (fuel : Nat) (assignment : Assignment) : ExceptT CloudError M Unit :=
  match mode with
  | .sequential => SequentialReplay.run store blobs (program input) fuel assignment
  | .parallel => ParallelReplay.run blobs (program input) fuel assignment

def batch (mode : Mode) (resume : Assignment → ExceptT CloudError M Unit)
    (assignments : List Assignment) : ExceptT CloudError M Unit :=
  match mode with
  | .sequential => assignments.forM resume
  | .parallel => ParallelReplay.children resume assignments

def follow (mode : Mode) (resume : Assignment → ExceptT CloudError M Unit)
    (branch : Location) : Progress → ExceptT CloudError M Unit
  | .done => pure ()
  | .fork location count => do
      batch mode resume ((List.range count).map fun index => ⟨0, location.child index⟩)
      resume ⟨0, branch⟩

def finish (mode : Mode) (fuel : Nat) (branch : Location) (action : Action) : ExceptT CloudError M Unit := do
  let progress ← action fuel
  follow mode (run blobs program input mode (fuel - 1)) branch progress

theorem run_succ (mode : Mode) (fuel : Nat) (assignment : Assignment) :
    run blobs program input mode (fuel + 1) assignment =
      finish blobs program input mode (fuel + 1) assignment.branchStart (steps blobs program input assignment) := by
  cases mode <;>
    simp [run, finish, steps, SequentialReplay.run, ParallelReplay.run, SequentialReplay.follow,
      ParallelReplay.follow, follow, batch, List.forM_map] <;> rfl

private theorem common_bound (items : List κ) (property : κ → Nat → Prop)
    (each : ∀ item ∈ items, ∃ bound, ∀ fuel, bound ≤ fuel → property item fuel) :
    ∃ bound, ∀ item ∈ items, ∀ fuel, bound ≤ fuel → property item fuel := by
  induction items with
  | nil => exact ⟨0, by simp⟩
  | cons item rest ih =>
    obtain ⟨a, first⟩ := each item (by simp)
    obtain ⟨b, later⟩ := ih (fun item member => each item (by simp [member]))
    refine ⟨max a b, ?_⟩
    intro other member fuel enough
    rcases List.mem_cons.mp member with rfl | member
    · exact first fuel (by omega)
    · exact later other member fuel (by omega)

/-- Both executable drivers realize the same finite replay reasoning. Their
only difference is how a batch supplies its child journals to the parent. -/
theorem Execution.runs {mode branch action before after}
      (execution : Execution (steps blobs program input) mode branch action before after) :
      ∃ bound, ∀ fuel, bound ≤ fuel → (finish blobs program input mode fuel branch action).run before = (.ok (), after) := by
    induction execution using Execution.rec
      (motive_2 := fun mode assignments before after _ =>
        ∃ bound, ∀ fuel, bound ≤ fuel →
          ((batch mode (run blobs program input mode fuel) assignments).run before) = (.ok (), after)) with
    | done returned =>
      obtain ⟨bound, returned⟩ := returned
      refine ⟨bound, fun fuel enough => ?_⟩
      simp only [finish, bind_run, returned fuel enough, follow, pure_run]
    | fork returned children resumed middle last =>
      obtain ⟨a, first⟩ := returned
      obtain ⟨b, middle⟩ := middle
      obtain ⟨c, last⟩ := last
      refine ⟨max a (max b c + 2), fun fuel enough => ?_⟩
      have positive : 0 < fuel - 1 := by omega
      obtain ⟨n, eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      simp only [finish, bind_run, first fuel (by omega), follow]
      rw [middle (fuel - 1) (by omega), eq, run_succ]
      exact last (n + 1) (by omega)
    | nil => exact ⟨0, by intros; rfl⟩
    | cons first rest firstRuns restRuns =>
      obtain ⟨a, first⟩ := firstRuns
      obtain ⟨b, rest⟩ := restRuns
      refine ⟨max a b + 1, fun fuel enough => ?_⟩
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
      simp only [batch, List.forM, bind_run]
      rw [run_succ, first (n + 1) (by omega)]
      exact rest (n + 1) (by omega)
    | @parallel before after κ items job journals children merged ih =>
      obtain ⟨bound, uniform⟩ := common_bound items _ ih
      refine ⟨bound + 1, fun fuel enough => ?_⟩
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by omega)
      have results : items.map (fun item =>
          ParallelReplay.worker (run blobs program input .parallel (n + 1)) before (job item)) =
          items.map (fun item => (.ok (), newRecords before (journals item))) := by
        apply List.map_congr_left
        intro item member
        unfold ParallelReplay.worker
        rw [run_succ, uniform item member (n + 1) (by omega)]
      simpa only [batch, ParallelReplay.children, bind_run, get_run, List.map_map, Task.spawn, Task.get,
        Function.comp_def, results] using merged

end LeanCloud.Proofs.ReplayExecution
