import LeanCloud.Proofs.SchedulerContracts
import LeanCloud.Proofs.WorkerDeployment

/-! Safety of the actual scheduler/worker deployment, from initial startup
through arbitrary process, network, and orphan-request events. The expected
journal is derived from the original pure source, not supplied runtime data. -/

namespace LeanCloud.Proofs.ConcurrentSafety
open Lean SimulationBackend ReplayModel SimulationLogic DeploymentContracts

theorem starts [codec : Codec α] (expected : Journal) (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩) :
    ∀ actor generation, ((system expected codec.encode (program input) workers).rules actor).Program
      (fun _ => True) (fun _ _ => True) (start turns fuel duration program input actor generation) := by
  intro actor generation
  by_cases zero : actor.val = 0
  · have same : actor = (⟨0, Nat.zero_lt_succ workers⟩ : Fin (workers + 1)) := Fin.ext zero
    subst actor
    simpa only [SimulationSafety.System.rules, system, beq_self_eq_true] using!
      SchedulerContracts.startup expected workers turns fuel duration program input generation
  · simpa only [SimulationSafety.System.rules, system, beq_eq_false_iff_ne.mpr zero] using!
      WorkerDeployment.startup expected workers turns fuel duration program input meaning known actor zero generation

/-- Every actual deployment trace preserves the shared invariant. There is no
assumed safety predicate for a trace or for suspended workers: startup and all
atomic contracts have been discharged against the existing actor code. -/
theorem reachable [codec : Codec α] (expected : Journal) (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    {after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) after) :
    (system expected codec.encode (program input) workers).Valid (fun _ _ _ => True) after := by
  let actors := start (workers := workers) turns fuel duration program input
  have valid := starts expected workers turns fuel duration program input meaning known
  have initial := (system expected codec.encode (program input) workers).initial {} actors (fun _ _ _ => True)
    (DeploymentContracts.initial expected codec.encode (program input)) valid
  exact (trace_preserves expected codec.encode (program input) workers actors (fun _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ => trivial) valid initial history).1

theorem invariant [codec : Codec α] (expected : Journal) (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    {after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) after) :
    Invariant expected codec.encode (program input) after.world :=
  (reachable expected workers turns fuel duration program input meaning known history).invariant

/-- Every continuation of a reachable execution preserves immutable records,
historical attempt identities, and completed jobs. This compares two actual
points in a deployment trace, including all intervening failures and messages. -/
theorem trace_advances [codec : Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome)
    {before after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) before)
    (continued : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True) before after) :
    Advance before.world after.world := by
  obtain ⟨expected, meaning, known⟩ := Specification.workflow_journal_exists evaluation codec.encode
  have safe := reachable expected workers turns fuel duration program input meaning known history
  exact (trace_preserves expected codec.encode (program input) workers (start turns fuel duration program input)
    (fun _ _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial)
    (starts expected workers turns fuel duration program input meaning known) safe continued).2

/-- Once a branch is marked done, no later actor, network, timer, or recovery
event can reopen it or remove it from the scheduler's durable job table. -/
theorem completed_branch_persists [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome)
    {before after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) before)
    (continued : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True) before after)
    (branch : Location) (completed : SchedulerProgress.Done before.world.scheduler.jobs branch) :
    SchedulerProgress.Done after.world.scheduler.jobs branch :=
  (trace_advances workers turns fuel duration program input evaluation history continued).completed.done completed

/-- Workflow completion is permanent, even if the scheduler crashes before
replying and later receives the same report again. -/
theorem completion_persists [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome)
    {before after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) before)
    (continued : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True) before after)
    (finished : before.world.scheduler.finished = true) : after.world.scheduler.finished = true :=
  (trace_advances workers turns fuel duration program input evaluation history continued).completed.finished finished

/-- A global root result, whenever it exists, is exactly the encoded outcome of
the original pure source. Crashes, redelivery, and stale attempts cannot publish
a different root result. No workflow completion or scheduling fairness is assumed. -/
theorem root_result [codec : Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome)
    {after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) after)
    (record : ReplayRecord) (present : after.world.records.lookup (ReplayStore.returnKey Location.root) = some record) :
    record = ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩ := by
  obtain ⟨expected, meaning, known⟩ := Specification.workflow_journal_exists evaluation codec.encode
  have safe := invariant expected workers turns fuel duration program input meaning known history
  exact Option.some.inj ((safe.records _ _ present).symm.trans known)

/-- Scheduler completion certifies that the correct root outcome is already
durable. This is a safety theorem; eventual completion needs progress assumptions. -/
theorem completed_result [codec : Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome)
    {after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) after)
    (finished : after.world.scheduler.finished = true) :
    after.world.records.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩ := by
  obtain ⟨expected, meaning, known⟩ := Specification.workflow_journal_exists evaluation codec.encode
  have safe := invariant expected workers turns fuel duration program input meaning known history
  obtain ⟨result, present⟩ := SchedulerRecords.finished_has_return after.world.scheduler after.world.records safe.completed finished
  have same := Option.some.inj ((safe.records _ _ present).symm.trans known)
  exact present.trans (congrArg some same)

/-- After any actual trace, an unfinished workflow still has pending or
assigned work. Its dependencies cannot all be stuck waiting on one another.
This does not assert that a live worker or sufficient execution fuel exists. -/
theorem unfinished_has_work [codec : Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome)
    {after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) after)
    (unfinished : after.world.scheduler.finished = false) :
    ∃ job ∈ after.world.scheduler.jobs,
      job.status = .pending ∨ ∃ worker attempt deadline, job.status = .running worker attempt deadline := by
  obtain ⟨expected, meaning, known⟩ := Specification.workflow_journal_exists evaluation codec.encode
  have safe := invariant expected workers turns fuel duration program input meaning known history
  exact SchedulerProgress.no_waiting_deadlock _ safe.progress unfinished

end LeanCloud.Proofs.ConcurrentSafety
