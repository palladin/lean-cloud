import LeanCloud.Proofs.ResumptionContracts
import LeanCloud.Proofs.Traffic

/-! Worker execution produces the semantic certificates required by the
scheduler's message contract. These are proofs of existing reports; the runtime
does not serialize proof witnesses, programs, or continuations. -/

namespace LeanCloud.Proofs.WorkerContracts
open Lean SimulationBackend ReplayModel SimulationLogic

def ReportResult (expected : Journal) (worker : WorkerId) (assignment : Checkpoint) (outcome : Exit)
    (encode : α → Json) (program : Cloud (SimM World) α) (report : Report) (world : World) : Prop :=
  report.worker = worker ∧ report.attempt = assignment.attempt ∧
    ExecutionContracts.Result expected assignment.branch outcome encode program Location.root report.progress world ∧
    ExecutionContracts.ForksAfter assignment assignment.location report.progress

/-- Reading observation keys preserves any stable interpreter postcondition,
including semantic results, replay paths, and fuel guarantees. -/
theorem execute [codec : Codec α] (expected : Journal) (worker : WorkerId) (assignment : Checkpoint)
    (fuel : Nat) (program : ι → Cloud (SimM World) α) (input : ι) (pre : World → Prop)
    (post : Except CloudError Progress → World → Prop)
    (stable : ∀ result, (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference (post result))
    (execution : (ReplayContracts.rules expected).Program pre post
      (ReplayInterpreter.step (observed worker).records blobs fuel program input assignment).run) :
    (ReplayContracts.rules expected).Program pre
      (fun report world => report.worker = worker ∧ report.attempt = assignment.attempt ∧ post report.progress world)
      (LeanCloud.Worker.execute worker (observed worker) blobs fuel program input assignment) := by
  apply Rules.bind _ execution
  intro progress
  apply Rules.bind _ (ReplayContracts.unchanged expected _ _ _
    (stable progress)
    (fun _ => rfl) (fun _ => ⟨rfl, rfl, rfl, rfl⟩))
  intro recorded
  exact fun _ _ holds => ⟨rfl, rfl, holds⟩

/-- Assignment validity supplies a proof checkpoint with a reconstructible
location and child-readiness certificate. Callers supply no journal snapshot,
typed continuation, or branch result. The source determines the result. -/
theorem assigned [codec : Codec α] (expected : Journal) (worker : WorkerId) (assignment : Checkpoint)
    (fuel : Nat) (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩) :
    (ReplayContracts.rules expected).Program
      (fun world => SchedulerGroups.AssignmentReady expected world.records assignment ∧
        Reconstruction.Resumable world.records codec.encode (program input) Location.root assignment.location)
      (fun report world => ∃ returned,
        expected.lookup (ReplayStore.returnKey assignment.branch) = some ⟨ReplayStore.returnRequest, returned⟩ ∧
        ReportResult expected worker assignment returned codec.encode (program input) report world)
      (LeanCloud.Worker.execute worker (observed worker) blobs fuel program input assignment) := by
  apply Rules.Program.weaken (required := fun world => ∃ journal,
    (Extends journal expected ∧ assignment.branch = Location.branchStart assignment.location ∧
      Reconstruction.Resumable journal codec.encode (program input) Location.root assignment.location) ∧
    (Extends journal world.records ∧ ExecutionContracts.Ready expected assignment world))
  · apply Rules.Program.exists_pre
    intro journal
    apply Rules.Program.assuming
    intro certificate
    obtain ⟨consistent, branch, resultType, encode, remaining, steps, witness⟩ := certificate
    obtain ⟨returned, returnedKnown, bound, bounded⟩ := ResumptionContracts.assigned expected journal worker assignment
      program input meaning known consistent branch witness
    apply Rules.Program.weaken_post _ _ (execute expected worker assignment fuel program input _
      (fun result world => ExecutionContracts.Result expected assignment.branch returned codec.encode
        (program input) Location.root result world ∧ ExecutionContracts.ForksAfter assignment assignment.location result)
      (fun result before after first last grows holds =>
        ⟨ExecutionContracts.result_stable expected assignment.branch returned codec.encode (program input) Location.root result
          before after first last grows holds.1, holds.2⟩)
      ((bounded fuel).weaken_post _ _ (fun _ _ _ holds => ⟨holds.1, holds.2.2⟩)))
    exact fun _ _ _ result => ⟨returned, returnedKnown, result⟩
  · intro world invariant ready
    exact ⟨world.records, ⟨invariant, ready.1.1, ready.2⟩, Extends.refl _, ready.1.2⟩

/-- Each reconstructible pure assignment has a sufficient fuel bound. Above
it, the actual worker report contains a fork or completion, never an interpreter
error. A workflow failure is still a valid durable completion. The precondition
requires only its recorded prefix and, for a join, the completed child records.
This is fuel adequacy; eventual delivery of atomic replies is a separate issue. -/
theorem sufficient_fuel [codec : Codec α] (expected journal : Journal) (worker : WorkerId)
    (assignment : Checkpoint) (program : ι → Cloud (SimM World) α) (input : ι)
    {β : Type} {remainingEncode : β → Json} {remaining : Cloud (SimM World) β} {steps outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    (consistent : Extends journal expected)
    (branch : assignment.branch = Location.branchStart assignment.location)
    (witness : Reconstruction.Prefix journal assignment.location codec.encode (program input)
      Location.root steps remainingEncode remaining) :
    ∃ bound, ∀ fuel, bound ≤ fuel → (ReplayContracts.rules expected).Program
      (fun world => Extends journal world.records ∧ ExecutionContracts.Ready expected assignment world)
      (fun report world => report.progress.isOk = true ∧ ∃ returned,
        expected.lookup (ReplayStore.returnKey assignment.branch) = some ⟨ReplayStore.returnRequest, returned⟩ ∧
        ReportResult expected worker assignment returned codec.encode (program input) report world)
      (LeanCloud.Worker.execute worker (observed worker) blobs fuel program input assignment) := by
  obtain ⟨returned, returnedKnown, bound, contract⟩ := ResumptionContracts.assigned expected journal worker assignment
    program input meaning known consistent branch witness
  refine ⟨bound, fun fuel enough => ?_⟩
  have stable : ∀ result, (ReplayContracts.rules expected).Stable (ReplayContracts.rules expected).interference
      (fun world => ExecutionContracts.Result expected assignment.branch returned codec.encode (program input) Location.root result world ∧
        ExecutionContracts.FuelBound fuel bound result ∧
        ExecutionContracts.ForksAfter assignment assignment.location result) :=
    fun result before after first last grows holds =>
      ⟨ExecutionContracts.result_stable expected assignment.branch returned codec.encode (program input) Location.root result
        before after first last grows holds.1, holds.2⟩
  apply Rules.Program.weaken_post _ _ (execute expected worker assignment fuel program input _ _ stable (contract fuel))
  intro report world invariant holds
  exact ⟨holds.2.2.2.1.isOk enough, returned, returnedKnown, holds.1, holds.2.1, holds.2.2.1, holds.2.2.2.2⟩

/-- A correctly identified assignment turns the actual worker's result into
exactly the message certificate required by the scheduler and durable transport.
Identity may be stale: an expired attempt cannot complete a different job. -/
theorem ReportResult.to_scheduler {expected worker assignment outcome world report}
    {encode : α → Json} {program : Cloud (SimM World) α}
    (result : ReportResult expected worker assignment outcome encode program report world)
    (identity : SchedulerAssignments.Identifies world.scheduler worker assignment) :
    Traffic.ToScheduler encode program expected world.scheduler world.records (.report report) := by
  refine ⟨by simpa [result.2.1] using identity.1, ?_, ?_, result.2.2.1.2, ?_⟩
  · intro job member deadline running completed
    have running' : job.status = .running worker assignment.attempt deadline := by
      simpa [result.1, result.2.1] using running
    have branch := congrArg Checkpoint.branch (identity.2 job member worker deadline running').2
    change job.branch = assignment.branch at branch
    refine ⟨outcome, ?_⟩
    rw [branch]
    have returned := result.2.2.1.1
    simpa [ExecutionContracts.Outcome, completed] using returned
  · intro job member deadline location count running forked
    have running' : job.status = .running worker assignment.attempt deadline := by
      simpa [result.1, result.2.1] using running
    have branch := congrArg Checkpoint.branch (identity.2 job member worker deadline running').2
    change job.branch = assignment.branch at branch
    rw [branch]
    have group := result.2.2.1.1
    simpa [ExecutionContracts.Outcome, forked] using group
  · intro job member deadline location count running forked
    have running' : job.status = .running worker assignment.attempt deadline := by
      simpa [result.1, result.2.1] using running
    have same := (identity.2 job member worker deadline running').2
    have advanced := result.2.2.2 location count forked
    have place : job.location = assignment.location := congrArg Checkpoint.location same
    have joining : job.joining = assignment.joining := congrArg Checkpoint.joining same
    simpa only [place, joining] using advanced

end LeanCloud.Proofs.WorkerContracts
