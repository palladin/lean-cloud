import LeanCloud.Proofs.WorkerProgress

/-! The original pure source bounds the number of productive scheduling
intervals. Each interval contains a real save of a live successful report;
arbitrary crashes, restarts, other workers, and network events may surround it.
This measures useful work, without assuming that a fair schedule supplies it. -/

namespace LeanCloud.Proofs.CoordinationProgress
open SimulationBackend

/-- An observation of a scheduler save, including the report still owned by
its durable mailbox. The surrounding trace verifies that these are real states.
The result may be a fork or completion; no correct outcome is assumed here. -/
def SavedReport (before after : World) : Prop :=
  ∃ report, SchedulerMessage.report report ∈ Mailbox.contents before.schedulerInbox ∧
    ∃ job ∈ before.scheduler.jobs, ∃ deadline,
      job.status = .running report.worker report.attempt deadline ∧
      report.progress.isOk = true ∧ after.scheduler.jobs = (Scheduler.Internal.accept before.scheduler report).jobs

/-- At least one live successful report is saved during this actual execution
interval. No bound is imposed on failures or unrelated events surrounding it. -/
def Productive (start : Simulation.Start World Unit count)
    (before after : Simulation.State World Unit count) : Prop :=
  ∃ first last,
    SchedulerOwnership.Trace start (fun _ => True) before first ∧
    SchedulerOwnership.Trace start (fun _ => True) first last ∧
    SavedReport first.world last.world ∧
    SchedulerOwnership.Trace start (fun _ => True) last after

theorem Productive.trace {start : Simulation.Start World Unit count} {before after}
    (productive : Productive start before after) : SchedulerOwnership.Trace start (fun _ => True) before after := by
  obtain ⟨first, last, approach, save, _, finish⟩ := productive
  exact (approach.trans save).trans finish

/-- A pure workflow admits only finitely many productive scheduling intervals.
The bound is determined before the worker count, budgets, schedule, and failures.
Successful accepted work cannot itself form an infinite execution. A separate
progress assumption is still needed to rule out indefinite failure or starvation. -/
theorem productive_intervals_bounded [codec : Codec α]
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (evaluation : Pure.Evaluation (program input) outcome) :
    ∃ capacity, ∀ workers turns fuel duration steps,
      ∀ states : Nat → Simulation.State World Unit (workers + 1),
      SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
        (Simulation.State.initial {} (start turns fuel duration program input)) (states 0) →
      (∀ index, index < steps → Productive (start turns fuel duration program input) (states index) (states (index + 1))) →
      steps ≤ capacity := by
  obtain ⟨limit, capacity, bounded⟩ := WorkerProgress.coordination_bounded program input evaluation
  refine ⟨capacity, ?_⟩
  intro workers turns fuel duration steps states initial opportunities
  have histories : ∀ index, index ≤ steps →
      SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
        (Simulation.State.initial {} (start turns fuel duration program input)) (states index) := by
    intro index
    induction index with
    | zero => exact fun _ => initial
    | succ index ih =>
      intro inside
      exact (ih (by omega)).trans (opportunities index (by omega)).trace
  have increasing : ∀ index, index ≤ steps → index ≤ SchedulerRank.rank limit (states index).world.scheduler.jobs := by
    intro index
    induction index with
    | zero => exact fun _ => Nat.zero_le _
    | succ index ih =>
      intro inside
      have previous := ih (by omega)
      have history := histories index (by omega)
      obtain ⟨first, last, approach, save, observation, finish⟩ := opportunities index (by omega)
      have firstHistory := history.trans approach
      have lastHistory := firstHistory.trans save
      obtain ⟨report, queued, job, member, deadline, running, success, saved⟩ := observation
      have increases := (bounded workers turns fuel duration first firstHistory).2 report queued job member deadline running success
      rw [← saved] at increases
      have before := (ConcurrentSafety.trace_advances workers turns fuel duration program input evaluation history approach).rank limit
      have after := (ConcurrentSafety.trace_advances workers turns fuel duration program input evaluation lastHistory finish).rank limit
      omega
  exact Nat.le_trans (increasing steps (Nat.le_refl _))
    (bounded workers turns fuel duration (states steps) (histories steps (Nat.le_refl _))).1

end LeanCloud.Proofs.CoordinationProgress
