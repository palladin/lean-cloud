import LeanCloud.Proofs.Scheduler
import LeanCloud.Proofs.SchedulerAssignments
import LeanCloud.Proofs.Specification

namespace LeanCloud.Proofs.SchedulerRecords
open LeanCloud.Scheduler Internal ReplayModel

/-- Every completed scheduler job has a durable branch return. Its value is
checked separately against the pure specification through `Extends`. -/
def DoneRecords (journal : Journal) (jobs : Array Job) : Prop :=
  ∀ job ∈ jobs, job.status = .done → ∃ outcome,
    journal.lookup (ReplayStore.returnKey job.branch) = some ⟨ReplayStore.returnRequest, outcome⟩

/-- A completion report is backed by a durable return record for any current
assignment it can complete. Stale reports impose no obligation. -/
def ReportBacked (journal : Journal) (state : State) (report : Report) : Prop :=
  ∀ job ∈ state.jobs, ∀ deadline,
    job.status = .running report.worker report.attempt deadline →
    report.progress = .ok .done → ∃ outcome,
      journal.lookup (ReplayStore.returnKey job.branch) = some ⟨ReplayStore.returnRequest, outcome⟩

/-- A live fork report identifies a specified group in its assigned branch.
Its certificate remains meaningful after the attempt expires. -/
def ForkBacked (expected : Journal) (state : State) (report : Report) : Prop :=
  ∀ job ∈ state.jobs, ∀ deadline location count,
    job.status = .running report.worker report.attempt deadline →
    report.progress = .ok (.fork location count) →
      job.branch = Location.branchStart location ∧ Specification.Group expected location count

def MessageBacked (journal : Journal) (state : State) : SchedulerMessage → Prop
  | .report report => ReportBacked journal state report
  | _ => True

theorem DoneRecords.extend {before after jobs} (completed : DoneRecords before jobs)
    (extension : Extends before after) : DoneRecords after jobs := by
  intro job member done
  obtain ⟨outcome, present⟩ := completed job member done
  exact ⟨outcome, extension _ _ present⟩

theorem ReportBacked.extend {before after state report} (backed : ReportBacked before state report)
    (extension : Extends before after) : ReportBacked after state report := by
  intro job member deadline running done
  obtain ⟨outcome, present⟩ := backed job member deadline running done
  exact ⟨outcome, extension _ _ present⟩

/-- A report may wait in a durable mailbox while other messages are handled.
Advancing the scheduler cannot redirect its old attempt to a different job. -/
theorem ReportBacked.advance {journal before after report} (backed : ReportBacked journal before report)
    (old : report.attempt < before.nextAttempt) (forward : SchedulerAssignments.Forward before after) :
    ReportBacked journal after report := by
  intro job member deadline running done
  exact backed job (forward.2 job member report.worker report.attempt deadline running old) deadline running done

/-- Advancing the scheduler cannot attach a delayed fork report to a different
branch, even if its original attempt has expired. -/
theorem ForkBacked.advance {expected before after report} (backed : ForkBacked expected before report)
    (old : report.attempt < before.nextAttempt) (forward : SchedulerAssignments.Forward before after) :
    ForkBacked expected after report := by
  intro job member deadline location count running forked
  exact backed job (forward.2 job member report.worker report.attempt deadline running old)
    deadline location count running forked

theorem initial (journal : Journal) : DoneRecords journal ({} : State).jobs := by
  intro job member done
  simp only [Array.mem_singleton] at member
  subst job
  cases done

theorem replace_done {journal jobs} (completed : DoneRecords journal jobs) (index : Nat)
    (replacement : Job)
    (backed : replacement.status = .done → ∃ outcome,
      journal.lookup (ReplayStore.returnKey replacement.branch) = some ⟨ReplayStore.returnRequest, outcome⟩) :
    DoneRecords journal (jobs.set! index replacement) := by
  intro job member done
  rcases Array.mem_or_eq_of_mem_setIfInBounds member with member | same
  · exact completed job member done
  · subst job
    exact backed done

private theorem mapped {journal jobs} (completed : DoneRecords journal jobs) (f : Job → Job)
    (retains : ∀ job, (f job).status = .done → (f job).branch = job.branch ∧ job.status = .done) :
    DoneRecords journal (jobs.map f) := by
  intro job member done
  obtain ⟨original, originalMember, rfl⟩ := Array.mem_map.mp member
  obtain ⟨branch, status⟩ := retains original done
  simpa only [branch] using completed original originalMember status

theorem awaken_preserves (state : State) (journal : Journal) (completed : DoneRecords journal state.jobs) :
    DoneRecords journal (awaken state).jobs := by
  apply mapped completed
  intro job done
  cases status : job.status <;> simp_all
  split at done <;> simp_all

theorem addChildren_preserves (journal : Journal) (jobs : Array Job) (children : Array Location)
    (completed : DoneRecords journal jobs) : DoneRecords journal (addChildren jobs children) := by
  apply Array.foldl_induction (fun _ current => DoneRecords journal current) completed
  intro index current ih
  split
  · exact ih
  · intro job member done
    rcases Array.mem_push.mp member with member | same
    · exact ih job member done
    · subst job
      cases done

theorem acquire_preserves (state : State) (journal : Journal) (worker : WorkerId) (duration : Nat)
    (completed : DoneRecords journal state.jobs) :
    DoneRecords journal (acquire state worker duration).1.jobs := by
  simp only [acquire]
  split
  · exact completed
  · split
    · exact completed
    · split
      · exact completed
      · split
        · apply replace_done completed
          intro impossible
          cases impossible
        · exact completed

theorem accept_preserves (state : State) (journal : Journal) (report : Report)
    (completed : DoneRecords journal state.jobs) (backed : ReportBacked journal state report) :
    DoneRecords journal (accept state report).jobs := by
  simp only [accept, Scheduler.observe_jobs]
  split
  next index found =>
    obtain ⟨member, deadline, running⟩ := Scheduler.report_job state report index found
    cases progress : report.progress with
    | error error => exact completed
    | ok result =>
      cases result with
      | done =>
        apply awaken_preserves
        apply replace_done completed
        intro _
        exact backed (state.jobs[index]!) member deadline running progress
      | fork location count =>
        apply awaken_preserves
        apply addChildren_preserves
        apply replace_done completed
        intro impossible
        cases impossible
  next =>
    change DoneRecords journal (observe state report.worker report.recorded).jobs
    simpa only [Scheduler.observe_jobs] using completed

/-- Expiring an assignment makes it pending; it cannot fabricate a completion. -/
theorem tick_preserves (state : State) (journal : Journal) (duration elapsed : Nat)
    (completed : DoneRecords journal state.jobs) :
    DoneRecords journal (handle duration state (.tick elapsed)).1.jobs := by
  apply mapped completed
  intro job done
  cases status : job.status <;> simp_all
  split at done <;> simp_all

/-- Restart preserves the relationship between completion metadata and global
returns, even though ownership of in-flight assignments is discarded. -/
theorem recover_preserves (state : State) (journal : Journal) (completed : DoneRecords journal state.jobs) :
    DoneRecords journal (Recovery.recovered state).jobs := by
  apply mapped completed
  intro job done
  cases status : job.status <;> simp_all

/-- Every actual scheduler transition preserves durable completion. The sole
transition that introduces `done` requires a report backed by its return record. -/
theorem handle_preserves (state : State) (journal : Journal) (duration : Nat) (message : SchedulerMessage)
    (completed : DoneRecords journal state.jobs) (backed : MessageBacked journal state message) :
    DoneRecords journal (handle duration state message).1.jobs := by
  cases message with
  | ready worker =>
    apply acquire_preserves
    simpa only [Scheduler.observe_jobs] using completed
  | report report => exact accept_preserves state journal report completed backed
  | inspect replyTo => exact completed
  | tick elapsed => exact tick_preserves state journal duration elapsed completed

/-- Scheduler completion means the global root return already exists. -/
theorem finished_has_return (state : State) (journal : Journal)
    (completed : DoneRecords journal state.jobs) (finished : state.finished = true) :
    ∃ outcome, journal.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, outcome⟩ := by
  simp only [State.finished, Array.any_eq_true', Bool.and_eq_true, beq_iff_eq, Scheduler.done_iff] at finished
  obtain ⟨job, member, branch, status⟩ := finished
  simpa only [branch] using completed job member status

end LeanCloud.Proofs.SchedulerRecords
