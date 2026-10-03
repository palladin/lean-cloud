import LeanCloud.Proofs.Recovery

namespace LeanCloud.Proofs.Scheduler
open LeanCloud.Scheduler Internal

theorem observe_jobs (state : State) (worker : WorkerId) (keys : Array String) :
    (observe state worker keys).jobs = state.jobs := by
  simp [observe]
  split <;> rfl

/-- The report lookup selects an existing job owned by that worker and attempt. -/
theorem report_job (state : State) (report : Report) (index : Nat)
    (found : state.jobs.findIdx? (fun job => match job.status with
      | .running worker attempt _ => worker == report.worker && attempt == report.attempt
      | _ => false) = some index) :
    state.jobs[index]! ∈ state.jobs ∧
      ∃ deadline, state.jobs[index]!.status = .running report.worker report.attempt deadline := by
  obtain ⟨inside, selected, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
  rw [getElem!_pos state.jobs index inside]
  refine ⟨Array.getElem_mem inside, ?_⟩
  cases current : state.jobs[index].status <;> simp only [current, Bool.false_eq_true] at selected
  rename_i owner attempt deadline
  simp only [Bool.and_eq_true_iff, beq_iff_eq] at selected
  obtain ⟨rfl, rfl⟩ := selected
  exact ⟨deadline, rfl⟩

/-- Acquisition copies an existing job's branch, replay location, and join mode,
whether it allocates a new attempt or resends an old assignment. -/
theorem acquire_from_job (state : State) (worker : WorkerId) (duration : Nat) (issued : Assignment)
    (sent : (acquire state worker duration).2 = .execute issued) :
    ∃ job ∈ state.jobs, ∃ attempt, assignment job attempt = issued := by
  cases error : state.error with
  | some errorValue => simp [acquire, error] at sent
  | none =>
    by_cases finished : state.finished = true
    · simp [acquire, error, finished] at sent
    · cases existing : state.jobs.findSome? (assignedTo worker) with
      | some old =>
        have same : old = issued := by simpa [acquire, error, finished, existing] using sent
        subst issued
        obtain ⟨job, member, owned⟩ := Array.exists_of_findSome?_eq_some existing
        cases status : job.status with
        | pending | waiting _ | done => simp [assignedTo, status] at owned
        | running owner attempt deadline =>
          simp only [assignedTo, status] at owned
          split at owned
          · cases owned; exact ⟨job, member, attempt, rfl⟩
          · contradiction
      | none =>
        cases pending : state.jobs.findIdx? (fun job => job.status == .pending) with
        | none => simp [acquire, error, finished, existing, pending] at sent
        | some index =>
          have same : assignment state.jobs[index]! state.nextAttempt = issued := by
            simpa [acquire, error, finished, existing, pending] using sent
          obtain ⟨inside, _, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp pending
          refine ⟨state.jobs[index]!, ?_, state.nextAttempt, same⟩
          rw [getElem!_pos state.jobs index inside]
          exact Array.getElem_mem inside

/-- Every execute message is issued from durable job metadata. -/
theorem handle_from_job (state : State) (duration : Nat) (message : SchedulerMessage)
    (delivery : Delivery) (issued : Assignment) (sent : delivery ∈ (handle duration state message).2)
    (executes : delivery.message = .execute issued) :
    ∃ job ∈ state.jobs, ∃ attempt, assignment job attempt = issued := by
  cases message with
  | ready worker =>
    change delivery ∈ #[⟨worker, (acquire (observe state worker #[]) worker duration).2⟩] at sent
    have same := Array.mem_singleton.mp sent
    subst delivery
    simpa only [observe_jobs] using acquire_from_job (observe state worker #[]) worker duration issued executes
  | report report =>
    simp only [handle, Array.mem_singleton] at sent
    subst delivery
    cases executes
  | inspect replyTo =>
    simp only [handle, Array.mem_singleton] at sent
    subst delivery
    cases executes
  | tick elapsed => simp [handle] at sent

theorem observe_error (state : State) (worker : WorkerId) (keys : Array String) :
    (observe state worker keys).error = state.error := by
  simp [observe]
  split <;> rfl

/-- Even a successful or failed report cannot change jobs unless its worker and
attempt match a currently running assignment. Observed record keys may be added. -/
theorem stale_report_preserves_progress (state : State) (duration : Nat) (report : Report)
    (stale : ∀ job ∈ state.jobs, ∀ deadline,
      job.status ≠ .running report.worker report.attempt deadline) :
    let after := (handle duration state (.report report)).1
    after.jobs = state.jobs ∧ after.error = state.error := by
  have absent : state.jobs.findIdx? (fun job =>
      match job.status with
      | .running worker attempt _ => worker == report.worker && attempt == report.attempt
      | _ => false) = none := by
    apply Array.findIdx?_eq_none_iff.mpr
    intro job member
    cases status : job.status with
    | running worker attempt deadline =>
      change (worker == report.worker && attempt == report.attempt) = false
      apply Bool.eq_false_iff.mpr
      intro matched
      obtain ⟨sameWorker, sameAttempt⟩ := Bool.and_eq_true_iff.mp matched
      simp only [beq_iff_eq] at sameWorker sameAttempt
      subst worker; subst attempt
      exact stale job member deadline status
    | pending | waiting _ | done => simp
  simp only [handle, accept, observe_jobs]
  erw [absent]
  exact ⟨observe_jobs .., observe_error ..⟩

/-- Before new assignments are issued after restart, any report from the old
processes can update observations but cannot change recovered job progress. -/
theorem recovered_report_preserves_progress (state : State) (duration : Nat) (report : Report) :
    let recovered := Recovery.recovered state
    let after := (handle duration recovered (.report report)).1
    after.jobs = recovered.jobs ∧ after.error = recovered.error := by
  apply stale_report_preserves_progress
  intro job member deadline
  exact Recovery.releases_assignments state job member report.worker report.attempt deadline

theorem done_iff (status : Status) : (status == .done) = true ↔ status = .done := by
  cases status <;> simp [BEq.beq, instBEqStatus.beq]

/-- A partial join becomes runnable only when every child is already marked done.
The scheduler does not evaluate child results or select a winning error. -/
theorem join_requires_completed_children (state : State) (index : Nat)
    (inside : index < state.jobs.size) (children : Array Location)
    (waiting : state.jobs[index].status = .waiting children)
    (resumed : ((awaken state).jobs[index]'(by simpa [awaken] using inside)).status = .pending) :
    ∀ child ∈ children, ∃ job ∈ state.jobs, job.branch = child ∧ job.status = .done := by
  have completed : children.all (fun child =>
      state.jobs.any (fun job => job.branch == child && job.status == .done)) = true := by
    simp only [awaken, Array.getElem_map, waiting] at resumed
    split at resumed
    · assumption
    · simp [waiting] at resumed
  simpa only [Array.all_eq_true', Array.any_eq_true', Bool.and_eq_true, beq_iff_eq, done_iff]
    using completed

end LeanCloud.Proofs.Scheduler
