import LeanCloud.Proofs.ConcurrentSafety
import LeanCloud.Proofs.SimulationProgress

/-! Progress of a worker segment from an actual reachable deployment state.
The source workflow and scheduler invariants supply its reconstruction path and
sufficient budget. An uninterrupted attempt can then produce a valid report.
Delivery and acceptance of that report remain separate progress obligations. -/

namespace LeanCloud.Proofs.WorkerProgress
open Lean SimulationBackend ReplayModel

/-- Every reachable job can produce a report in finitely many uninterrupted
Sim steps, given sufficient fuel. The report is a fork or completion; completion
already has a durable branch return. The bound is for this job and snapshot.
This does not claim an arbitrary schedule provides the required opportunity. -/
theorem job_can_report [codec : Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome)
    {current : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) current)
    (job : Scheduler.Job) (member : job ∈ current.world.scheduler.jobs)
    (worker : WorkerId) (attempt : Nat) :
    ∃ bound, ∀ budget, bound ≤ budget →
      let assignment := Scheduler.Internal.assignment job attempt
      let action := LeanCloud.Worker.execute worker (observed worker) blobs budget program input assignment
      let run : Simulation.Start World Report 1 := fun _ _ => action
      ∃ events report final,
        (∀ event ∈ events, event = .commit 0 ∨ event = .resume 0) ∧
        Simulation.run run events (Simulation.State.initial current.world run) = .ok final ∧
        final.actors 0 = .finished report ∧
        report.worker = worker ∧ report.attempt = attempt ∧ report.progress.isOk = true ∧
        ExecutionContracts.ForksAfter assignment job.location report.progress ∧
        (report.progress = .ok .done → ∃ record,
          final.world.records.lookup (ReplayStore.returnKey job.branch) = some record) := by
  obtain ⟨expected, meaning, known⟩ := Specification.workflow_journal_exists evaluation codec.encode
  have safe := ConcurrentSafety.invariant expected workers turns fuel duration program input meaning known history
  have ready := safe.groups job member
  obtain ⟨β, encode, remaining, steps, path⟩ := safe.paths job member
  let assignment := Scheduler.Internal.assignment job attempt
  obtain ⟨bound, contract⟩ := WorkerContracts.sufficient_fuel expected current.world.records worker assignment
    program input meaning known safe.records ready.branch path
  refine ⟨bound, fun budget enough => ?_⟩
  dsimp only
  let run : Simulation.Start World Report 1 := fun _ _ =>
    LeanCloud.Worker.execute worker (observed worker) blobs budget program input assignment
  let initial := Simulation.State.initial current.world run
  obtain ⟨events, report, world, onlyActor, finished, _, success, returned, returnedKnown, sound⟩ :=
    SimulationProgress.completes (ReplayContracts.rules expected) run 0 (contract budget enough) initial
      rfl safe.records ⟨Extends.refl _, ready.ready⟩
  refine ⟨events, report, { initial.setActor 0 (.finished report) with world }, onlyActor, finished,
    by simp [Simulation.State.setActor], sound.1, sound.2.1, success, sound.2.2.2, ?_⟩
  intro completed
  refine ⟨⟨ReplayStore.returnRequest, returned⟩, ?_⟩
  simpa [ExecutionContracts.Outcome, completed, assignment, Scheduler.Internal.assignment] using sound.2.2.1.1

/-- A pure source determines a finite set of possible branch identities,
independently of scheduling, worker count, crashes, and retries. Every reachable
job's return key belongs to that set; execution cannot invent new branches.
This bounds distinct identities, not the number of attempts or trace events. -/
theorem branch_keys_finite [codec : Codec α]
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome) :
    ∃ keys : List String, ∀ workers turns fuel duration,
      ∀ current : Simulation.State World Unit (workers + 1),
      SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
        (Simulation.State.initial {} (start turns fuel duration program input)) current →
      ∀ job ∈ current.world.scheduler.jobs, ReplayStore.returnKey job.branch ∈ keys := by
  obtain ⟨expected, meaning, known⟩ := Specification.workflow_journal_exists evaluation codec.encode
  refine ⟨expected.map Prod.fst, ?_⟩
  intro workers turns fuel duration current history job member
  have safe := ConcurrentSafety.invariant expected workers turns fuel duration program input meaning known history
  exact safe.branch_keys meaning known job member

/-- The pure source gives one finite bound on useful coordination work, before
worker count, scheduling, crashes, or retries are chosen. Every reachable state
is below that bound. Saving a successful live report strictly advances the same
measure, so those saves cannot repeat indefinitely. Report availability and
sufficient execution opportunities remain separate obligations. -/
theorem coordination_bounded [codec : Codec α]
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome) :
    ∃ limit capacity, ∀ workers turns fuel duration,
      ∀ current : Simulation.State World Unit (workers + 1),
      SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
        (Simulation.State.initial {} (start turns fuel duration program input)) current →
      SchedulerRank.rank limit current.world.scheduler.jobs ≤ capacity ∧
      ∀ report, SchedulerMessage.report report ∈ Mailbox.contents current.world.schedulerInbox →
        ∀ job ∈ current.world.scheduler.jobs, ∀ deadline,
          job.status = .running report.worker report.attempt deadline → report.progress.isOk = true →
          SchedulerRank.rank limit current.world.scheduler.jobs <
            SchedulerRank.rank limit (Scheduler.Internal.accept current.world.scheduler report).jobs := by
  obtain ⟨expected, meaning, known⟩ := Specification.workflow_journal_exists evaluation codec.encode
  obtain ⟨limit, bounded⟩ := SchedulerRank.group_bound expected
  refine ⟨limit, expected.length * (3 * limit + 3), ?_⟩
  intro workers turns fuel duration current history
  have safe := ConcurrentSafety.invariant expected workers turns fuel duration program input meaning known history
  have size : current.world.scheduler.jobs.size ≤ expected.length := by
    simpa using safe.unique.size_le (expected.map Prod.fst) (safe.branch_keys meaning known)
  refine ⟨Nat.le_trans (SchedulerRank.rank_le limit _) (Nat.mul_le_mul_right _ size), ?_⟩
  intro report queued job member deadline running success
  have message := safe.messages.scheduler (.report report) queued
  apply SchedulerRank.accept_increases limit current.world.scheduler report job deadline
    safe.assignments member running success (safe.groups job member).branch
  intro location count forked
  obtain ⟨same, group⟩ := message.2.2.1 job member deadline location count running forked
  obtain ⟨forward, joining⟩ := message.2.2.2.2 job member deadline location count running forked
  exact ⟨same, forward, joining, bounded location count group⟩

end LeanCloud.Proofs.WorkerProgress
