import LeanCloud.Proofs.WorkerContracts
import Init.Data.List.Nat.Basic

/-! A single source-dependent fuel budget for every assignment of a pure
workflow. Each location has one typed replay path across compatible snapshots;
only finitely many branch starts and forks can be assigned. The bound is a proof
witness, not a precomputed journal or another runtime interpreter. -/

namespace LeanCloud.Proofs.WorkerFuel
open Lean LeanEff SimulationBackend ReplayModel SimulationLogic Reconstruction

private theorem inverse_keys (keys : List String) (key : Location → String)
    (injective : ∀ {first last}, key first = key last → first = last) :
    ∃ locations : List Location, ∀ location, key location ∈ keys → location ∈ locations := by
  classical
  induction keys with
  | nil => exact ⟨[], by simp⟩
  | cons name names ih =>
    obtain ⟨locations, covered⟩ := ih
    by_cases found : ∃ location, key location = name
    · obtain ⟨location, same⟩ := found
      refine ⟨location :: locations, ?_⟩
      intro target member
      rcases List.mem_cons.mp member with head | rest
      · exact List.mem_cons.mpr (Or.inl (injective (head.trans same.symm)))
      · exact List.mem_cons.mpr (Or.inr (covered target rest))
    · refine ⟨locations, ?_⟩
      intro location member
      rcases List.mem_cons.mp member with head | rest
      · exact False.elim (found ⟨location, head⟩)
      · exact covered location rest

private theorem locations_finite (expected : Journal) :
    ∃ locations : List Location, ∀ location,
      (expected.lookup (ReplayStore.returnKey location)).isSome = true ∨
      (expected.lookup (ReplayStore.valueKey location)).isSome = true → location ∈ locations := by
  obtain ⟨branches, branchKeys⟩ := inverse_keys (expected.map Prod.fst) ReplayStore.returnKey Location.return_key_injective
  obtain ⟨forks, forkKeys⟩ := inverse_keys (expected.map Prod.fst) ReplayStore.valueKey Location.value_key_injective
  have member : ∀ key, (expected.lookup key).isSome = true → key ∈ expected.map Prod.fst := by
    intro key present
    obtain ⟨entry, inside, same⟩ := List.lookup_isSome_iff.mp present
    exact List.mem_map.mpr ⟨entry, inside, (beq_iff_eq.mp same).symm⟩
  exact ⟨branches ++ forks, fun location present => present.elim
    (fun found => List.mem_append.mpr (Or.inl (branchKeys location (member _ found))))
    (fun found => List.mem_append.mpr (Or.inr (forkKeys location (member _ found))))⟩

/-- The bound is fixed before workers, assignments, snapshots, and interleaving
are selected. Above it, every valid assignment produces a fork or completion;
a workflow failure remains a normal recorded completion, not a worker error. -/
theorem step [codec : Codec α] (expected : Journal)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩) :
    ∃ bound, ∀ worker (assignment : Checkpoint) fuel, bound ≤ fuel →
      (ReplayContracts.rules expected).Program
        (fun world => SchedulerGroups.AssignmentReady expected world.records assignment ∧
          Resumable world.records codec.encode (program input) Location.root assignment.location)
        (fun result _ => result.isOk = true)
        (ReplayInterpreter.step (observed worker).records blobs fuel program input assignment).run := by
  classical
  obtain ⟨locations, covered⟩ := locations_finite expected
  let Sufficient := fun target bound => ∀ worker (assignment : Checkpoint),
    assignment.location = target → assignment.branch = Location.branchStart target →
    ∀ journal, Extends journal expected → Resumable journal codec.encode (program input) Location.root target →
    ∀ fuel, bound ≤ fuel → (ReplayContracts.rules expected).Program
      (fun world => Extends journal world.records ∧ ExecutionContracts.Ready expected assignment world)
      (fun result _ => result.isOk = true)
      (ReplayInterpreter.step (observed worker).records blobs fuel program input assignment).run
  have budgets : ∀ target, ∃ bound, Resumable expected codec.encode (program input) Location.root target → Sufficient target bound := by
    intro target
    by_cases available : Resumable expected codec.encode (program input) Location.root target
    · obtain ⟨bound, valid⟩ := ResumptionContracts.location_fuel expected target program input meaning known available
      exact ⟨bound, fun _ => valid⟩
    · exact ⟨0, fun path => False.elim (available path)⟩
  let cost := fun target => Classical.choose (budgets target)
  let bound := (locations.map cost).max?.getD 0
  refine ⟨bound, ?_⟩
  intro worker assignment fuel enough
  apply Rules.Program.weaken (required := fun world => ∃ journal,
    (Extends journal expected ∧ SchedulerGroups.AssignmentReady expected journal assignment ∧
      Resumable journal codec.encode (program input) Location.root assignment.location) ∧
    (Extends journal world.records ∧ ExecutionContracts.Ready expected assignment world))
  · apply Rules.Program.exists_pre
    intro journal
    apply Rules.Program.assuming
    rintro ⟨consistent, ready, available⟩
    have target : assignment.location ∈ locations := by
      apply covered
      rcases ready.origin with same | ⟨count, group⟩
      · obtain ⟨β, remainingEncode, remaining, steps, witness⟩ := available
        obtain ⟨result, _, returned⟩ := meaning.resume (by simpa using known) witness consistent
        rw [← ready.branch, ← same] at returned
        exact Or.inl (by simp [returned])
      · obtain ⟨α, codec, outcomes, present, _⟩ := group
        exact Or.inr (by simp [present])
    have selected : cost assignment.location ≤ bound :=
      List.le_max?_getD_of_mem (List.mem_map.mpr ⟨assignment.location, target, rfl⟩)
    exact Classical.choose_spec (budgets assignment.location) (available.extend consistent)
      worker assignment rfl ready.branch journal consistent available fuel (Nat.le_trans selected enough)
  · intro world consistent ready
    exact ⟨world.records, ⟨consistent, ready⟩, Extends.refl _, ready.1.ready⟩

/-- The same source-wide budget applies to the report published by the worker.
No assumption about the returned result is required from the environment. -/
theorem execute [codec : Codec α] (expected : Journal)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩) :
    ∃ bound, ∀ worker (assignment : Checkpoint) fuel, bound ≤ fuel →
      (ReplayContracts.rules expected).Program
        (fun world => SchedulerGroups.AssignmentReady expected world.records assignment ∧
          Resumable world.records codec.encode (program input) Location.root assignment.location)
        (fun report _ => report.progress.isOk = true)
        (LeanCloud.Worker.execute worker (observed worker) blobs fuel program input assignment) := by
  obtain ⟨bound, valid⟩ := step expected program input meaning known
  refine ⟨bound, ?_⟩
  intro worker assignment fuel enough
  apply Rules.Program.weaken_post _ _ (WorkerContracts.execute expected worker assignment fuel program input _ _
    (fun _ _ _ _ _ _ holds => holds) (valid worker assignment fuel enough))
  exact fun _ _ _ holds => holds.2.2

end LeanCloud.Proofs.WorkerFuel
