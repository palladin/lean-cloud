import LeanCloud.Proofs.CoordinationProgress
import LeanCloud.Proofs.WorkerFuel
import LeanCloud.Proofs.DeploymentExecution

/-! Completion under explicit processing opportunities. The environment must
eventually allow a delivered assignment to execute, its report to reach the
scheduler while live, and the scheduler to save it. It need not supply a
successful result: sufficient source-wide fuel proves that from the actual
worker program. Other actors may run between the selected worker's operations;
arbitrary failures may occur before it gets such a processing opportunity. -/

namespace LeanCloud.Proofs.DeploymentProgress
open Lean SimulationBackend Reconstruction

/-- An execution is sampled after finite batches of actual simulator events.
Each batch may include actor steps, crashes, restarts, and network operations. -/
structure Run (actors : Simulation.Start World Unit count) where
  state : Nat → Simulation.State World Unit count
  initial : state 0 = Simulation.State.initial {} actors
  next : ∀ index, SchedulerOwnership.Trace actors (fun _ => True) (state index) (state (index + 1))

theorem Run.reachable {actors : Simulation.Start World Unit count} (run : Run actors) (index : Nat) :
    SchedulerOwnership.Trace actors (fun _ => True) (Simulation.State.initial {} actors) (run.state index) := by
  induction index with
  | zero => rw [run.initial]; exact .refl _
  | succ index ih => exact ih.trans (run.next index)

/-- One timely processing opportunity, stated using the existing worker and
scheduler operations. Its endpoints and intermediate states belong to the
actual deployment trace. The selected computation must finish, but other actors
and broker events may interleave with its atomic operations. Delivery may take
arbitrarily many finite events, provided the report is still live when saved.
No successful progress or expected workflow value is assumed. -/
def Window [Codec α] (actors : Simulation.Start World Unit count) (fuel : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι)
    (before after : Simulation.State World Unit count) : Prop :=
  ∃ started executed delivered saved worker assignment report,
    SchedulerOwnership.Trace actors (fun _ => True) before started ∧
    WorkerMessage.execute assignment ∈ Mailbox.contents ((started.world.workerInboxes.lookup worker).getD {}) ∧
    DeploymentExecution.Execution actors
      (LeanCloud.Worker.execute worker (observed worker) blobs fuel program input assignment)
      started report executed ∧
    SchedulerOwnership.Trace actors (fun _ => True) executed delivered ∧
    SchedulerMessage.report report ∈ Mailbox.contents delivered.world.schedulerInbox ∧
    (∃ job ∈ delivered.world.scheduler.jobs, ∃ deadline,
      job.status = .running report.worker report.attempt deadline) ∧
    SchedulerOwnership.Trace actors (fun _ => True) delivered saved ∧
    saved.world.scheduler.jobs = (Scheduler.Internal.accept delivered.world.scheduler report).jobs ∧
    SchedulerOwnership.Trace actors (fun _ => True) saved after

/-- These are sufficient delivery/execution/restart opportunities, not weak
fairness alone. They exclude endless crashes, expiry before every report, and
actor-loop exhaustion that prevents further processing. They do not assume
that any branch or the workflow completes. -/
def MakesProgress [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι)
    (run : Run (start (workers := workers) turns fuel duration program input)) : Prop :=
  ∀ index, (run.state index).world.scheduler.finished = false →
    ∃ later, index < later ∧ Window (start turns fuel duration program input) fuel program input
      (run.state index) (run.state later)

/-- The source-wide execution budget makes a processing window productive.
The assignment and report certificates come from the actual reachable trace;
the worker's success comes from its verified interpreter contract. -/
theorem window_productive [codec : Codec α] (expected : ReplayModel.Journal)
    (workers turns fuel duration : Nat) (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    (budget : ∀ worker assignment, (ReplayContracts.rules expected).Program
      (fun world => SchedulerGroups.AssignmentReady expected world.records assignment ∧
        Resumable world.records codec.encode (program input) Location.root assignment.location)
      (fun report _ => report.progress.isOk = true)
      (LeanCloud.Worker.execute worker (observed worker) blobs fuel program input assignment))
    {before after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) before)
    (window : Window (start turns fuel duration program input) fuel program input before after) :
    CoordinationProgress.Productive (start turns fuel duration program input) before after := by
  obtain ⟨started, executed, delivered, saved, worker, assignment, report,
    approach, queued, execution, transported, received, ⟨job, member, deadline, running⟩,
    committed, stored, finish⟩ := window
  have safe := ConcurrentSafety.invariant expected workers turns fuel duration program input meaning known (history.trans approach)
  have ready := Traffic.inbox_valid safe.messages worker (.execute assignment) queued
  obtain ⟨_, cached⟩ := meaning.cached
  have successful := execution.post (ReplayContracts.rules expected) _
    (fun _ reached => (ConcurrentSafety.invariant expected workers turns fuel duration program input meaning known reached).records)
    (fun _ _ reached continued =>
      (ConcurrentSafety.trace_advances workers turns fuel duration program input cached.evaluation reached continued).records)
    (budget worker assignment) (history.trans approach) ready.2
  exact ⟨delivered, saved, (approach.trans execution.trace).trans transported, committed,
    ⟨report, received, job, member, deadline, running, successful, stored⟩, finish⟩

/-- Sufficient fuel and recurring timely processing windows force completion.
The finite-work bound is derived from the original pure source. In particular,
the environment does not supply `finished`, a correct result, or successful
worker reports as premises. -/
theorem eventually_finishes [codec : Codec α]
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome) :
    ∃ sufficientFuel, ∀ workers turns fuel duration, sufficientFuel ≤ fuel →
      ∀ run : Run (start (workers := workers) turns fuel duration program input),
      MakesProgress workers turns fuel duration program input run →
      ∃ index, (run.state index).world.scheduler.finished = true := by
  classical
  obtain ⟨expected, meaning, known⟩ := Specification.workflow_journal_exists evaluation codec.encode
  obtain ⟨sufficientFuel, budget⟩ := WorkerFuel.execute expected program input meaning known
  obtain ⟨capacity, bounded⟩ := CoordinationProgress.productive_intervals_bounded program input evaluation
  refine ⟨sufficientFuel, ?_⟩
  intro workers turns fuel duration enough run progress
  apply Classical.byContradiction
  intro never
  have unfinished : ∀ index, (run.state index).world.scheduler.finished = false := by
    intro index
    apply Bool.eq_false_iff.mpr
    exact fun finished => never ⟨index, finished⟩
  let next := fun index => Classical.choose (progress index (unfinished index))
  have opportunity := fun index => Classical.choose_spec (progress index (unfinished index))
  let visit : Nat → Nat := Nat.rec 0 (fun _ index => next index)
  have windows : ∀ index, CoordinationProgress.Productive (start turns fuel duration program input)
      (run.state (visit index)) (run.state (visit (index + 1))) := by
    intro index
    simpa only [visit, next] using window_productive expected workers turns fuel duration program input meaning known
      (fun worker assignment => budget worker assignment fuel enough) (run.reachable (visit index))
      (opportunity (visit index)).2
  have impossible := bounded workers turns fuel duration (capacity + 1) (fun index => run.state (visit index))
    (by simpa only [visit] using! run.reachable 0) (fun index _ => windows index)
  omega

end LeanCloud.Proofs.DeploymentProgress
