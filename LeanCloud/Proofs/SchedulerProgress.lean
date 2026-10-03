import LeanCloud.Proofs.SchedulerGroups
import Init.Data.List.Nat.Basic

/-! The scheduler's dependency graph cannot strand all unfinished jobs at joins.
This is a prerequisite for liveness, not an assumption about worker fairness. -/

namespace LeanCloud.Proofs.SchedulerProgress
open LeanCloud.Scheduler Internal

def Has (jobs : Array Job) (branch : Location) : Prop :=
  ∃ job ∈ jobs, job.branch = branch

def Done (jobs : Array Job) (branch : Location) : Prop :=
  ∃ job ∈ jobs, job.branch = branch ∧ job.status = .done

theorem awaken_keeps_done (state : State) {branch : Location} (completed : Done state.jobs branch) :
    Done (awaken state).jobs branch := by
  obtain ⟨job, member, same, done⟩ := completed
  refine ⟨job, ?_, same, done⟩
  apply Array.mem_map.mpr
  exact ⟨job, member, by simp [done]⟩

theorem awaken_keeps_job (state : State) {branch : Location} (present : Has state.jobs branch) :
    Has (awaken state).jobs branch := by
  obtain ⟨job, member, same⟩ := present
  refine ⟨_, Array.mem_map.mpr ⟨job, member, rfl⟩, ?_⟩
  cases job.status <;> simp only
  all_goals first | exact same | (split <;> exact same)

private theorem awaken_waiting (state : State) (job : Job) (children : Array Location)
    (member : job ∈ state.jobs) (waiting : job.status = .waiting children) :
    ∃ updated ∈ (awaken state).jobs,
      updated.branch = job.branch ∧ updated.location = job.location ∧
      (updated.status = .waiting children ∨ updated.status = .pending ∧ updated.joining = true) := by
  by_cases ready : children.all (fun child => state.jobs.any (fun job => job.branch == child && job.status == .done)) = true
  · refine ⟨{ job with status := .pending, joining := true }, ?_, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩
    exact Array.mem_map.mpr ⟨job, member, by simp [waiting, ready]⟩
  · refine ⟨job, ?_, rfl, rfl, Or.inl waiting⟩
    exact Array.mem_map.mpr ⟨job, member, by simp [waiting, ready]⟩

/-- A completion report for an attempt that is still live marks that branch
done. The database save in the scheduler turn makes this transition durable. -/
theorem completion_marks_done (state : State) (report : Report) (job : Job) (deadline : Nat)
    (valid : SchedulerAssignments.Valid state) (member : job ∈ state.jobs)
    (running : job.status = .running report.worker report.attempt deadline)
    (completed : report.progress = .ok .done) : Done (accept state report).jobs job.branch := by
  obtain ⟨index, found, selected⟩ := SchedulerAssignments.live_report_selects state report job deadline valid member running
  have inside := (Array.findIdx?_eq_some_iff_getElem.mp found).1
  simp only [accept, Scheduler.observe_jobs]
  erw [found]
  simp only [completed]
  apply awaken_keeps_done
  refine ⟨{ job with status := .done }, ?_, rfl, rfl⟩
  simpa only [Scheduler.observe_jobs, selected, Array.set!_eq_setIfInBounds] using
    (Array.mem_setIfInBounds (a := { job with status := .done }) inside)

/-- All dependencies exist and point to deeper branches. -/
structure Linked (jobs : Array Job) : Prop where
  root : Has jobs Location.root
  children : ∀ job ∈ jobs, ∀ children, job.status = .waiting children →
    ∀ child ∈ children, Has jobs child ∧ job.branch.size < child.size

/-- A join whose children are all done is never left waiting. -/
def Awake (jobs : Array Job) : Prop :=
  ∀ job ∈ jobs, ∀ children, job.status = .waiting children →
    ¬ ∀ child ∈ children, Done jobs child

structure Valid (jobs : Array Job) : Prop where
  linked : Linked jobs
  awake : Awake jobs

theorem initial : Valid ({} : State).jobs := by
  refine ⟨⟨⟨⟨Location.root, Location.root, false, .pending⟩, by simp, rfl⟩, ?_⟩, ?_⟩
  all_goals
    intro job member children waiting
    simp only [Array.mem_singleton] at member
    subst job
    cases waiting

private theorem mapped_linked {jobs : Array Job} (valid : Linked jobs) (f : Job → Job)
    (branch : ∀ job, (f job).branch = job.branch)
    (waiting : ∀ job children, (f job).status = .waiting children → job.status = .waiting children) :
    Linked (jobs.map f) := by
  have keeps : ∀ location, Has jobs location → Has (jobs.map f) location := by
    intro location ⟨job, member, same⟩
    exact ⟨f job, Array.mem_map.mpr ⟨job, member, rfl⟩, (branch job).trans same⟩
  refine ⟨keeps _ valid.root, ?_⟩
  intro job member children suspended child inside
  obtain ⟨old, oldMember, rfl⟩ := Array.mem_map.mp member
  have linked := valid.children old oldMember children (waiting old children suspended) child inside
  exact ⟨keeps _ linked.1, by simpa only [branch] using linked.2⟩

private theorem mapped_awake {jobs : Array Job} (valid : Awake jobs) (f : Job → Job)
    (branch : ∀ job, (f job).branch = job.branch)
    (waiting : ∀ job children, (f job).status = .waiting children → job.status = .waiting children)
    (done : ∀ job, (f job).status = .done → job.status = .done) :
    Awake (jobs.map f) := by
  intro job member children suspended completed
  obtain ⟨old, oldMember, rfl⟩ := Array.mem_map.mp member
  apply valid old oldMember children (waiting old children suspended)
  intro child inside
  obtain ⟨found, present, same, finished⟩ := completed child inside
  obtain ⟨original, originalMember, rfl⟩ := Array.mem_map.mp present
  exact ⟨original, originalMember, (branch original).symm.trans same, done original finished⟩

private theorem mapped {jobs : Array Job} (valid : Valid jobs) (f : Job → Job)
    (branch : ∀ job, (f job).branch = job.branch)
    (waiting : ∀ job children, (f job).status = .waiting children → job.status = .waiting children)
    (done : ∀ job, (f job).status = .done → job.status = .done) : Valid (jobs.map f) :=
  ⟨mapped_linked valid.linked f branch waiting, mapped_awake valid.awake f branch waiting done⟩

private theorem set_has {jobs : Array Job} (index : Nat) (replacement : Job)
    (same : replacement.branch = jobs[index]!.branch) {location : Location} (present : Has jobs location) :
    Has (jobs.set! index replacement) location := by
  change Has (jobs.setIfInBounds index replacement) location
  obtain ⟨job, member, branch⟩ := present
  obtain ⟨position, inside, equal⟩ := Array.mem_iff_getElem.mp member
  refine ⟨(jobs.setIfInBounds index replacement)[position]'(by simpa using inside), Array.getElem_mem _, ?_⟩
  rw [Array.getElem_setIfInBounds inside]
  by_cases selected : index = position
  · subst index
    simp only [ite_true]
    rw [same, getElem!_pos jobs position inside, equal]
    exact branch
  · simpa [selected, equal] using branch

private theorem addChildren_facts (jobs : Array Job) (children : Array Location) :
    (∀ job ∈ jobs, job ∈ addChildren jobs children) ∧
    (∀ child ∈ children, Has (addChildren jobs children) child) ∧
    (∀ job ∈ addChildren jobs children, ∀ waiting, job.status = .waiting waiting → job ∈ jobs) := by
  by_cases empty : children = #[]
  · subst children
    exact ⟨fun _ member => member, by simp, fun _ member _ _ => member⟩
  · obtain ⟨children, child, rfl⟩ := Array.exists_push_of_ne_empty empty
    have ih := addChildren_facts jobs children
    have step : addChildren jobs (children.push child) =
        if (addChildren jobs children).any (fun job => job.branch == child) then addChildren jobs children
        else (addChildren jobs children).push ⟨child, child, false, .pending⟩ := by
      simp only [addChildren, Array.foldl_push]
      rfl
    rw [step]
    split
    next found =>
      refine ⟨ih.1, ?_, ih.2.2⟩
      intro location member
      rcases Array.mem_push.mp member with member | rfl
      · exact ih.2.1 location member
      · simpa only [Array.any_eq_true', beq_iff_eq, Has] using found
    next missing =>
      refine ⟨fun job member => Array.mem_push.mpr (Or.inl (ih.1 job member)), ?_, ?_⟩
      · intro location member
        rcases Array.mem_push.mp member with member | rfl
        · obtain ⟨job, present, same⟩ := ih.2.1 location member
          exact ⟨job, Array.mem_push.mpr (Or.inl present), same⟩
        · exact ⟨_, Array.mem_push.mpr (Or.inr rfl), rfl⟩
      · intro job member waiting suspended
        rcases Array.mem_push.mp member with member | rfl
        · exact ih.2.2 job member waiting suspended
        · cases suspended
termination_by children.size

/-- A live fork report records its suspension and creates every child job.
The parent either waits for those children or becomes a runnable join if they
are already complete, including an empty parallel group. -/
theorem fork_schedules_children (state : State) (report : Report) (job : Job) (deadline : Nat)
    (location : Location) (count : Nat)
    (valid : SchedulerAssignments.Valid state) (member : job ∈ state.jobs)
    (running : job.status = .running report.worker report.attempt deadline)
    (forked : report.progress = .ok (.fork location count)) :
    (∃ updated ∈ (accept state report).jobs,
      updated.branch = job.branch ∧ updated.location = location ∧
      (updated.status = .waiting ((Array.range count).map location.child) ∨
        updated.status = .pending ∧ updated.joining = true)) ∧
    ∀ index : Fin count, Has (accept state report).jobs (location.child index) := by
  obtain ⟨index, found, selected⟩ := SchedulerAssignments.live_report_selects state report job deadline valid member running
  have inside := (Array.findIdx?_eq_some_iff_getElem.mp found).1
  let children := (Array.range count).map location.child
  let suspended := { job with location, joining := false, status := .waiting children }
  let jobs := addChildren (state.jobs.set! index suspended) children
  have added := addChildren_facts (state.jobs.set! index suspended) children
  have parent : suspended ∈ jobs := added.1 _ (Array.mem_setIfInBounds inside)
  simp only [accept, Scheduler.observe_jobs]
  erw [found]
  simp only [forked, selected]
  refine ⟨?_, ?_⟩
  · exact awaken_waiting _ suspended children parent rfl
  · intro child
    apply awaken_keeps_job
    apply added.2.1
    exact Array.mem_map.mpr ⟨child.val, by simp, rfl⟩

private theorem replace_linked {jobs : Array Job} (valid : Linked jobs)
    (index : Nat) (replacement : Job) (children : Array Location)
    (branch : replacement.branch = jobs[index]!.branch)
    (waiting : ∀ required, replacement.status = .waiting required →
      required = children ∧ ∀ child ∈ children, replacement.branch.size < child.size) :
    Linked (addChildren (jobs.set! index replacement) children) := by
  have added := addChildren_facts (jobs.set! index replacement) children
  have keeps : ∀ location, Has jobs location → Has (addChildren (jobs.set! index replacement) children) location := by
    intro location present
    obtain ⟨job, member, same⟩ := set_has index replacement branch present
    exact ⟨job, added.1 job member, same⟩
  refine ⟨keeps _ valid.root, ?_⟩
  intro job member required suspended child inside
  have old := added.2.2 job member required suspended
  rcases Array.mem_or_eq_of_mem_setIfInBounds old with old | rfl
  · have linked := valid.children job old required suspended child inside
    exact ⟨keeps _ linked.1, linked.2⟩
  · obtain ⟨rfl, deeper⟩ := waiting required suspended
    exact ⟨added.2.1 child inside, deeper child inside⟩

private theorem replace_awake {jobs : Array Job} (valid : Awake jobs) (index : Nat) (replacement : Job)
    (waiting : ∀ children, replacement.status ≠ .waiting children)
    (done : replacement.status ≠ .done) : Awake (jobs.set! index replacement) := by
  intro job member children suspended completed
  rcases Array.mem_or_eq_of_mem_setIfInBounds member with member | rfl
  · apply valid job member children suspended
    intro child inside
    obtain ⟨found, present, branch, finished⟩ := completed child inside
    rcases Array.mem_or_eq_of_mem_setIfInBounds present with present | rfl
    · exact ⟨found, present, branch, finished⟩
    · exact False.elim (done finished)
  · exact False.elim (waiting children suspended)

private theorem replace {jobs : Array Job} (valid : Valid jobs) (index : Nat) (replacement : Job)
    (branch : replacement.branch = jobs[index]!.branch)
    (waiting : ∀ children, replacement.status ≠ .waiting children)
    (done : replacement.status ≠ .done) : Valid (jobs.set! index replacement) := by
  refine ⟨?_, replace_awake valid.awake index replacement waiting done⟩
  simpa only [addChildren, Array.foldl_empty] using
    replace_linked valid.linked index replacement #[] branch (fun children same => False.elim (waiting children same))

/-- Awakening is sufficient to restore the no-blocked-ready-join property;
it does not depend on which completion or fork report triggered the scan. -/
theorem awaken_preserves (state : State) (linked : Linked state.jobs) : Valid (awaken state).jobs := by
  have branch : ∀ job : Job, (match job.status with
      | .waiting children => if children.all (fun child => state.jobs.any (fun j => j.branch == child && j.status == Status.done)) then
          { job with status := .pending, joining := true } else job
      | _ => job).branch = job.branch := by
    intro job
    cases job.status <;> simp only
    all_goals first | rfl | (split <;> rfl)
  constructor
  · apply mapped_linked linked _ branch
    intro job children suspended
    cases status : job.status <;> simp_all
    split at suspended <;> simp_all
  · intro job member children suspended completed
    obtain ⟨old, oldMember, rfl⟩ := Array.mem_map.mp member
    cases status : old.status with
    | pending | running _ _ _ | done => simp [status] at suspended
    | waiting waitingChildren =>
      simp only [status] at suspended
      split at suspended
      · cases suspended
      next notReady =>
        have sameChildren : waitingChildren = children := by simpa [status] using suspended
        subst children
        apply notReady
        simp only [Array.all_eq_true', Array.any_eq_true', Bool.and_eq_true, beq_iff_eq, Scheduler.done_iff]
        intro child inside
        obtain ⟨found, present, same, finished⟩ := completed child inside
        obtain ⟨original, originalMember, rfl⟩ := Array.mem_map.mp present
        refine ⟨original, originalMember, (branch original).symm.trans same, ?_⟩
        cases status : original.status <;> simp_all
        split at finished <;> simp_all

theorem acquire_preserves (state : State) (worker : WorkerId) (duration : Nat) (valid : Valid state.jobs) :
    Valid (acquire state worker duration).1.jobs := by
  simp only [acquire]
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact valid
      · split
        · exact replace valid _ _ rfl (by intro _ impossible; cases impossible) (by intro impossible; cases impossible)
        · exact valid

/-- Accepted forks retain their parent and insert every dependency before the
join can wait for it. Completion always scans for newly ready joins. -/
theorem accept_preserves (state : State) (report : Report) (expected : ReplayModel.Journal)
    (valid : Valid state.jobs) (forked : SchedulerRecords.ForkBacked expected state report) :
    Valid (accept state report).jobs := by
  simp only [accept, Scheduler.observe_jobs]
  split
  next index found =>
    obtain ⟨member, deadline, running⟩ := Scheduler.report_job state report index found
    cases progress : report.progress with
    | error error => exact valid
    | ok result =>
      cases result with
      | done =>
        apply awaken_preserves
        simpa only [addChildren, Array.foldl_empty] using replace_linked valid.linked index
          { state.jobs[index]! with status := .done } #[] rfl (by intro _ impossible; cases impossible)
      | fork location count =>
        apply awaken_preserves
        apply replace_linked valid.linked index
          { state.jobs[index]! with location, joining := false, status := .waiting ((Array.range count).map location.child) }
          ((Array.range count).map location.child) rfl
        intro required suspended
        cases suspended
        refine ⟨rfl, ?_⟩
        intro child inside
        obtain ⟨childIndex, _, rfl⟩ := Array.mem_map.mp inside
        have branch := (forked _ member deadline location count running progress).1
        simp only [branch, Location.branchStart, Array.size_set!, LeanCloud.Location.child, Array.size_push]
        omega
  next =>
    change Valid (observe state report.worker report.recorded).jobs
    simpa only [Scheduler.observe_jobs] using valid

theorem tick_preserves (state : State) (duration elapsed : Nat) (valid : Valid state.jobs) :
    Valid (handle duration state (.tick elapsed)).1.jobs := by
  apply mapped valid
  · intro job
    cases job.status <;> simp only
    all_goals first | rfl | (split <;> rfl)
  · intro job children waiting
    cases status : job.status <;> simp_all
    split at waiting <;> simp_all
  · intro job done
    cases status : job.status <;> simp_all
    split at done <;> simp_all

theorem recover_preserves (state : State) (valid : Valid state.jobs) :
    Valid (Recovery.recovered state).jobs := by
  apply mapped valid
  · intro job
    cases job.status <;> rfl
  · intro job children waiting
    cases status : job.status <;> simp_all
  · intro job done
    cases status : job.status <;> simp_all

theorem handle_preserves (state : State) (duration : Nat) (message : SchedulerMessage)
    (expected : ReplayModel.Journal) (valid : Valid state.jobs)
    (forked : match (generalizing := false) message with
      | .report report => SchedulerRecords.ForkBacked expected state report | _ => True) :
    Valid (handle duration state message).1.jobs := by
  cases message with
  | ready worker =>
    apply acquire_preserves
    simpa only [Scheduler.observe_jobs] using valid
  | report report => exact accept_preserves state report expected valid forked
  | inspect replyTo => exact valid
  | tick elapsed => exact tick_preserves state duration elapsed valid

private def depth (jobs : Array Job) : Nat :=
  (jobs.toList.map (fun job => job.branch.size)).max?.getD 0

private theorem depth_bound {jobs : Array Job} {job : Job} (member : job ∈ jobs) :
    job.branch.size ≤ depth jobs :=
  List.le_max?_getD_of_mem (List.mem_map.mpr ⟨job, by simpa using member, rfl⟩)

private theorem unfinished_has_work (jobs : Array Job) (valid : Valid jobs)
    (job : Job) (member : job ∈ jobs) (unfinished : job.status ≠ .done) :
    ∃ ready ∈ jobs, ready.status = .pending ∨ ∃ worker attempt deadline, ready.status = .running worker attempt deadline := by
  cases status : job.status with
  | pending => exact ⟨job, member, Or.inl status⟩
  | running worker attempt deadline => exact ⟨job, member, Or.inr ⟨worker, attempt, deadline, status⟩⟩
  | done => exact False.elim (unfinished status)
  | waiting children =>
    classical
    have missing := valid.awake job member children status
    simp only [Classical.not_forall] at missing
    obtain ⟨child, inside, missing⟩ := missing
    obtain ⟨⟨descendant, present, branch⟩, deeper⟩ := valid.linked.children job member children status child inside
    exact unfinished_has_work jobs valid descendant present (fun done => missing ⟨descendant, present, branch, done⟩)
termination_by depth jobs - job.branch.size
decreasing_by
  have bound := depth_bound present
  rw [← branch] at deeper
  omega

/-- Until the root completes, at least one job is pending or assigned to a
worker. Finite, strictly deeper dependencies cannot form a waiting deadlock. -/
theorem no_waiting_deadlock (state : State) (valid : Valid state.jobs)
    (unfinished : state.finished = false) :
    ∃ job ∈ state.jobs, job.status = .pending ∨ ∃ worker attempt deadline, job.status = .running worker attempt deadline := by
  obtain ⟨root, member, branch⟩ := valid.linked.root
  apply unfinished_has_work state.jobs valid root member
  intro done
  have finished : state.finished = true := Array.any_eq_true'.mpr ⟨root, member, by simp [branch, done, Scheduler.done_iff]⟩
  simp_all

/-- Restart releases assignments and leaves an unfinished graph with pending
work. Recovery cannot leave every surviving job blocked on another join. -/
theorem recovery_has_pending (state : State) (valid : Valid state.jobs)
    (unfinished : state.finished = false) :
    ∃ job ∈ (Recovery.recovered state).jobs, job.status = .pending := by
  have unfinished' : (Recovery.recovered state).finished = false :=
    (Recovery.preserves_completion state).trans unfinished
  obtain ⟨job, member, pending | ⟨worker, attempt, deadline, running⟩⟩ :=
    no_waiting_deadlock _ (recover_preserves state valid) unfinished'
  · exact ⟨job, member, pending⟩
  · exact False.elim (Recovery.releases_assignments state job member worker attempt deadline running)

/-- A ready worker is given an assignment whenever pending work exists and
the scheduler has no terminal result or protocol error. -/
theorem acquire_executes (state : State) (worker : WorkerId) (duration : Nat)
    (healthy : state.error = none) (unfinished : state.finished = false)
    (pending : ∃ job ∈ state.jobs, job.status = .pending) :
    ∃ assignment, (acquire state worker duration).2 = .execute assignment := by
  cases assigned : state.jobs.findSome? (assignedTo worker) with
  | some issued => exact ⟨issued, by simp [acquire, healthy, unfinished, assigned]⟩
  | none =>
    cases found : state.jobs.findIdx? (fun job => job.status == .pending) with
    | some index => exact ⟨assignment state.jobs[index]! state.nextAttempt, by simp [acquire, healthy, unfinished, assigned, found]⟩
    | none =>
      obtain ⟨job, member, status⟩ := pending
      have absent := Array.findIdx?_eq_none_iff.mp found job member
      rw [status] at absent
      contradiction

/-- The actual ready-message handler emits an assignment for available work. -/
theorem ready_executes (state : State) (worker : WorkerId) (duration : Nat)
    (healthy : state.error = none) (unfinished : state.finished = false)
    (pending : ∃ job ∈ state.jobs, job.status = .pending) :
    ∃ assignment, (handle duration state (.ready worker)).2 = #[⟨worker, .execute assignment⟩] := by
  obtain ⟨assignment, sent⟩ := acquire_executes (observe state worker #[]) worker duration
    ((Scheduler.observe_error ..).trans healthy)
    (by simpa only [State.finished, Scheduler.observe_jobs] using unfinished)
    (by simpa only [Scheduler.observe_jobs] using pending)
  exact ⟨assignment, by simpa only [handle] using congrArg (fun message => #[Delivery.mk worker message]) sent⟩

/-- A healthy unfinished scheduler can issue work immediately after recovery,
without needing another completion report or timer tick to unlock its graph. -/
theorem recovery_executes (state : State) (worker : WorkerId) (duration : Nat)
    (valid : Valid state.jobs) (healthy : state.error = none) (unfinished : state.finished = false) :
    ∃ assignment, (handle duration (Recovery.recovered state) (.ready worker)).2 = #[⟨worker, .execute assignment⟩] := by
  obtain ⟨_, _, _, _, sameError⟩ := Recovery.preserves_metadata state
  exact ready_executes _ worker duration (sameError.trans healthy)
    ((Recovery.preserves_completion state).trans unfinished) (recovery_has_pending state valid unfinished)

end LeanCloud.Proofs.SchedulerProgress
