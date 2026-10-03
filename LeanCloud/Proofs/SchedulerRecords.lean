import LeanCloud.Proofs.Scheduler
import LeanCloud.Proofs.SchedulerAssignments
import LeanCloud.Proofs.Recording
import LeanCloud.Proofs.Segment
import LeanCloud.Worker

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

/-- The actual worker reporting code produces `done` only after the step has
persisted its result. Reading observation keys may not alter replay records.
Fork reports identify a specified group in the assigned branch. Assignment
identity comes from issuance and survives subsequent transitions. -/
theorem execute_report_backed [Codec α] (expected journal : Journal) (state : State)
    (worker : WorkerId) (assignment : Assignment) (blobs : BlobStorage M) (fuel : Nat)
    (program : ι → Cloud M α) (input : ι) (outcome : Exit)
    (confirmed : M (Array String)) (readOnly : ∀ records, (confirmed.run records).2 = records)
    (safe : Segment.Safe expected assignment.branch outcome journal
      ((ReplayInterpreter.step store blobs fuel program input assignment).run journal))
    (identity : SchedulerAssignments.Identifies state worker assignment) :
    let observed : LeanCloud.Worker.ObservedStore M := ⟨store, confirmed⟩
    let (report, after) := (LeanCloud.Worker.execute worker observed blobs fuel program input assignment).run journal
    report.attempt < state.nextAttempt ∧ ReportBacked after state report ∧ ForkBacked expected state report := by
  let execution := (ReplayInterpreter.step store blobs fuel program input assignment).run journal
  change assignment.attempt < state.nextAttempt ∧ ReportBacked (confirmed.run execution.2).2 state
    ⟨worker, assignment.attempt, execution.1, (confirmed.run execution.2).1⟩ ∧
    ForkBacked expected state ⟨worker, assignment.attempt, execution.1, (confirmed.run execution.2).1⟩
  rw [readOnly]
  refine ⟨identity.1, ?_, ?_⟩
  · intro job member deadline running done
    refine ⟨outcome, ?_⟩
    have branch := congrArg Assignment.branch (identity.2 job member worker deadline running).2
    change job.branch = assignment.branch at branch
    rw [branch]
    exact safe.completed done
  · intro job member deadline location count running forked
    have branch := congrArg Assignment.branch (identity.2 job member worker deadline running).2
    change job.branch = assignment.branch at branch
    rw [branch]
    exact safe.forked location count forked

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

/-- A group made runnable by the scheduler has every required child return in
global storage. Child reports may arrive in any order. -/
theorem awakened_children_have_returns (state : State) (journal : Journal) (index : Nat)
    (inside : index < state.jobs.size) (children : Array Location)
    (completed : DoneRecords journal state.jobs)
    (waiting : state.jobs[index].status = .waiting children)
    (resumed : ((awaken state).jobs[index]'(by simpa [awaken] using inside)).status = .pending) :
    ∀ child ∈ children, ∃ outcome, journal.lookup (ReplayStore.returnKey child) =
      some ⟨ReplayStore.returnRequest, outcome⟩ := by
  intro child member
  obtain ⟨job, member, branch, done⟩ :=
    Scheduler.join_requires_completed_children state index inside children waiting resumed child member
  simpa only [branch] using completed job member done

/-- The scheduler's wakeup condition establishes the interpreter's join
precondition when stored records agree with the pure specification. -/
theorem awakened_join_is_ready (state : State) (expected journal : Journal) (index : Nat)
    (inside : index < state.jobs.size) (location : Location) (count : Nat)
    (atLocation : state.jobs[index].location = location)
    (completed : DoneRecords journal state.jobs) (consistent : Extends journal expected)
    (waiting : state.jobs[index].status = .waiting ((Array.range count).map location.child))
    (resumed : ((awaken state).jobs[index]'(by simpa [awaken] using inside)).status = .pending)
    (group : Specification.Group expected location count) :
    Recording.JoinReady expected journal ((awaken state).jobs[index]'(by simpa [awaken] using inside)).location := by
  have sameLocation : ((awaken state).jobs[index]'(by simpa [awaken] using inside)).location = location := by
    simp only [awaken, Array.getElem_map, waiting]
    split <;> exact atLocation
  rw [sameLocation]
  apply Recording.JoinReady.of_group group consistent
  intro child
  exact awakened_children_have_returns state journal index inside _ completed waiting resumed
    (location.child child) (Array.mem_map.mpr ⟨child.val, Array.mem_range.mpr child.isLt, rfl⟩)

/-- Once the scheduler declares the root complete, its durable record decodes to
the direct interpreter's typed result. The hypotheses are the record invariants
preserved above and by worker execution; this is not yet a whole-Sim theorem. -/
theorem finished_matches_direct [codec : Codec α] (state : State) (expected journal : Journal)
    (blobs : BlobStorage M) (program : ι → Cloud M α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    (completed : DoneRecords journal state.jobs) (consistent : Extends journal expected)
    (finished : state.finished = true) (roundtrip : Pure.RoundTrips codec) :
    ∃ stored, journal.lookup (ReplayStore.returnKey Location.root) =
        some ⟨ReplayStore.returnRequest, stored⟩ ∧
      (ReplayInterpreter.result (m := Id) (α := α) stored).run =
        ((DirectInterpreter.interpret blobs program input).run []).1 := by
  obtain ⟨stored, present⟩ := finished_has_return state journal completed finished
  obtain ⟨steps, cached⟩ := meaning.cached
  exact ⟨stored, present, Segment.root_record_matches_direct expected journal blobs program input
    ⟨ReplayStore.returnRequest, stored⟩ cached known consistent present roundtrip⟩

end LeanCloud.Proofs.SchedulerRecords
