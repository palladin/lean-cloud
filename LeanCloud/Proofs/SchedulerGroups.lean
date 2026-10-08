import LeanCloud.Proofs.SchedulerRecords
import LeanCloud.Proofs.Recording
import LeanCloud.Proofs.Checkpoint

namespace LeanCloud.Proofs.SchedulerGroups
open LeanCloud.Scheduler Internal ReplayModel SchedulerRecords

/-- Waiting metadata names the specified children. A runnable parent already
has their returns in storage; the scheduler only checks completion markers. -/
structure JobValid (expected journal : Journal) (job : Job) : Prop where
  branch : job.branch = Location.branchStart job.location
  waiting : ∀ children, job.status = .waiting children →
    ∃ count, children = (Array.range count).map job.location.child ∧
      Specification.Group expected job.location count
  ready : job.joining = true → Recording.JoinReady expected journal job.location
  origin : job.location = job.branch ∨ ∃ count, Specification.Group expected job.location count

def Valid (expected journal : Journal) (jobs : Array Job) : Prop :=
  ∀ job ∈ jobs, JobValid expected journal job

/-- The checkpoint belongs to the assigned branch. A parent marked ready has
its child returns in storage. This proof certificate survives reassignment. -/
structure AssignmentReady (expected journal : Journal) (issued : Checkpoint) : Prop where
  branch : issued.branch = Location.branchStart issued.location
  ready : issued.joining = true → Recording.JoinReady expected journal issued.location
  origin : issued.location = issued.branch ∨ ∃ count, Specification.Group expected issued.location count

theorem AssignmentReady.extend {expected before after issued}
    (ready : AssignmentReady expected before issued) (extension : Extends before after) :
    AssignmentReady expected after issued :=
  ⟨ready.1, fun joining => (ready.2 joining).extend extension, ready.origin⟩

theorem JobValid.assignment {expected journal job} (valid : JobValid expected journal job) (attempt : Nat) :
    AssignmentReady expected journal (Checkpoint.ofJob job attempt) := ⟨valid.branch, valid.ready, valid.origin⟩

theorem Valid.extend {expected before after jobs} (valid : Valid expected before jobs)
    (extension : Extends before after) : Valid expected after jobs := by
  intro job member
  have old := valid job member
  exact ⟨old.branch, old.waiting, fun joining => (old.ready joining).extend extension, old.origin⟩

theorem initial (expected journal : Journal) : Valid expected journal ({} : State).jobs := by
  intro job member
  simp only [Array.mem_singleton] at member
  subst job
  exact ⟨by simp, (by intro children impossible; cases impossible), by simp, Or.inl rfl⟩

private theorem JobValid.with_status {expected journal job} (valid : JobValid expected journal job)
    (status : Status) (notWaiting : ∀ children, status ≠ .waiting children) :
    JobValid expected journal { job with status } :=
  ⟨valid.branch, fun children impossible => False.elim (notWaiting children impossible), valid.ready, valid.origin⟩

private theorem replace {expected journal jobs} (valid : Valid expected journal jobs)
    (index : Nat) (replacement : Job) (sound : JobValid expected journal replacement) :
    Valid expected journal (jobs.set! index replacement) := by
  intro job member
  rcases Array.mem_or_eq_of_mem_setIfInBounds member with member | same
  · exact valid job member
  · subst job; exact sound

private theorem mapped {expected journal jobs} (valid : Valid expected journal jobs) (f : Job → Job)
    (preserves : ∀ job ∈ jobs, JobValid expected journal job → JobValid expected journal (f job)) :
    Valid expected journal (jobs.map f) := by
  intro job member
  obtain ⟨original, present, rfl⟩ := Array.mem_map.mp member
  exact preserves original present (valid original present)

theorem awaken_preserves (state : State) (expected journal : Journal)
    (valid : Valid expected journal state.jobs) (completed : DoneRecords journal state.jobs)
    (consistent : Extends journal expected) : Valid expected journal (awaken state).jobs := by
  apply mapped valid
  intro job member sound
  cases status : job.status with
  | pending | running _ _ _ | done => simpa only [status] using sound
  | waiting children =>
    simp only
    split
    next allDone =>
      refine ⟨sound.branch, (by intro children impossible; cases impossible), ?_, sound.origin⟩
      intro _
      obtain ⟨count, sameChildren, group⟩ := sound.waiting children status
      apply Recording.JoinReady.of_group group consistent
      intro index
      rw [sameChildren] at allDone
      simp only [Array.all_eq_true', Array.any_eq_true', Bool.and_eq_true, beq_iff_eq, Scheduler.done_iff] at allDone
      obtain ⟨child, childMember, branch, done⟩ := allDone (job.location.child index)
        (Array.mem_map.mpr ⟨index.val, Array.mem_range.mpr index.isLt, rfl⟩)
      simpa only [branch] using completed child childMember done
    next => exact sound

theorem addChildren_preserves (expected journal : Journal) (jobs : Array Job) (children : Array Location)
    (valid : Valid expected journal jobs)
    (starts : ∀ child ∈ children, Location.branchStart child = child) :
    Valid expected journal (addChildren jobs children) := by
  apply Array.foldl_induction (fun _ current => Valid expected journal current) valid
  intro index current ih
  split
  · exact ih
  · intro job member
    rcases Array.mem_push.mp member with member | same
    · exact ih job member
    · subst job
      exact ⟨(starts _ (Array.getElem_mem _)).symm, (by intro children impossible; cases impossible), by simp, Or.inl rfl⟩

theorem acquire_preserves (state : State) (expected journal : Journal) (worker : WorkerId) (duration : Nat)
    (valid : Valid expected journal state.jobs) : Valid expected journal (acquire state worker duration).1.jobs := by
  simp only [acquire]
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact valid
      · split
        next index found =>
          obtain ⟨inside, _, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
          have member : state.jobs[index]! ∈ state.jobs := by
            rw [getElem!_pos state.jobs index inside]
            exact Array.getElem_mem inside
          exact replace valid index _ ((valid _ member).with_status _ (by intros; simp))
        next => exact valid

/-- Accepting a certified fork records the matching child set. Completion may
awaken joins only after the reported return has reached durable storage. -/
theorem accept_preserves (state : State) (expected journal : Journal) (report : Report)
    (valid : Valid expected journal state.jobs) (completed : DoneRecords journal state.jobs)
    (consistent : Extends journal expected) (backed : ReportBacked journal state report)
    (forked : ForkBacked expected state report) :
    Valid expected journal (accept state report).jobs := by
  simp only [accept, Scheduler.observe_jobs]
  split
  next index found =>
    obtain ⟨member, deadline, running⟩ := Scheduler.report_job state report index found
    cases progress : report.progress with
    | error error => exact valid
    | ok result =>
      cases result with
      | done =>
        apply awaken_preserves _ expected journal _ _ consistent
        · exact replace valid index _ ((valid _ member).with_status .done (by intros; simp))
        · exact replace_done completed index _ (fun _ => backed (state.jobs[index]!) member deadline running progress)
      | fork location count =>
        have sound := forked _ member deadline location count running progress
        apply awaken_preserves _ expected journal _ _ consistent
        · apply addChildren_preserves
          · apply replace valid
            refine ⟨sound.1, ?_, by simp, Or.inr ⟨count, sound.2⟩⟩
            intro children same
            cases same
            exact ⟨count, rfl, sound.2⟩
          · intro child member
            obtain ⟨index, _, rfl⟩ := Array.mem_map.mp member
            simp
        · apply SchedulerRecords.addChildren_preserves
          exact replace_done completed index _ (by intro impossible; cases impossible)
  next =>
    change Valid expected journal (observe state report.worker report.recorded).jobs
    simpa only [Scheduler.observe_jobs] using valid

theorem tick_preserves (state : State) (expected journal : Journal) (duration elapsed : Nat)
    (valid : Valid expected journal state.jobs) :
    Valid expected journal (handle duration state (.tick elapsed)).1.jobs := by
  apply mapped valid
  intro job member sound
  cases status : job.status with
  | pending | waiting _ | done => simpa only [status] using sound
  | running owner attempt deadline =>
    simp only
    split
    · exact sound.with_status .pending (by intros; simp)
    · exact sound

theorem recover_preserves (state : State) (expected journal : Journal)
    (valid : Valid expected journal state.jobs) :
    Valid expected journal (Recovery.recovered state).jobs := by
  apply mapped valid
  intro job member sound
  cases status : job.status with
  | pending | waiting _ | done => simpa only [status] using sound
  | running owner attempt deadline => exact sound.with_status .pending (by intros; simp)

/-- Every actual scheduler transition preserves specified waiting groups and
the child-return certificate of runnable parents. -/
theorem handle_preserves (state : State) (expected journal : Journal) (duration : Nat) (message : SchedulerMessage)
    (valid : Valid expected journal state.jobs) (completed : DoneRecords journal state.jobs)
    (consistent : Extends journal expected) (backed : MessageBacked journal state message)
    (forked : match (generalizing := false) message with | .report report => ForkBacked expected state report | _ => True) :
    Valid expected journal (handle duration state message).1.jobs := by
  cases message with
  | ready worker =>
    apply acquire_preserves
    simpa only [Scheduler.observe_jobs] using valid
  | report report => exact accept_preserves state expected journal report valid completed consistent backed forked
  | inspect replyTo => exact valid
  | tick elapsed => exact tick_preserves state expected journal duration elapsed valid

end LeanCloud.Proofs.SchedulerGroups
