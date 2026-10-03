import LeanCloud.Proofs.Scheduler

namespace LeanCloud.Proofs.SchedulerAssignments
open LeanCloud.Scheduler Internal

/-- Live attempts are below the durable allocation counter, and one attempt
cannot identify two different running jobs. -/
structure Valid (state : State) : Prop where
  bounded : ∀ job ∈ state.jobs, ∀ worker attempt deadline,
    job.status = .running worker attempt deadline → attempt < state.nextAttempt
  unique : ∀ first ∈ state.jobs, ∀ second ∈ state.jobs, ∀ owner₁ owner₂ attempt deadline₁ deadline₂,
    first.status = .running owner₁ attempt deadline₁ →
    second.status = .running owner₂ attempt deadline₂ → first = second

/-- Historical assignment identity remains meaningful after timeout: if its
attempt is still live, its owner, branch, location, and join mode are unchanged. -/
def Identifies (state : State) (worker : WorkerId) (issued : Assignment) : Prop :=
  issued.attempt < state.nextAttempt ∧
    ∀ job ∈ state.jobs, ∀ owner deadline,
      job.status = .running owner issued.attempt deadline →
      owner = worker ∧ assignment job issued.attempt = issued

/-- Old attempts cannot reappear as different jobs. New live attempts, if any,
are allocated at or above the preceding counter. -/
def Forward (before after : State) : Prop :=
  before.nextAttempt ≤ after.nextAttempt ∧
    ∀ job ∈ after.jobs, ∀ worker attempt deadline,
      job.status = .running worker attempt deadline → attempt < before.nextAttempt → job ∈ before.jobs

theorem Forward.refl (state : State) : Forward state state :=
  ⟨Nat.le_refl _, fun _ member _ _ _ _ _ => member⟩

theorem Forward.trans {first middle last} (earlier : Forward first middle) (later : Forward middle last) :
    Forward first last := by
  refine ⟨Nat.le_trans earlier.1 later.1, ?_⟩
  intro job member worker attempt deadline running old
  exact earlier.2 job (later.2 job member worker attempt deadline running (Nat.lt_of_lt_of_le old earlier.1))
    worker attempt deadline running old

theorem Identifies.advance {before after worker issued} (identity : Identifies before worker issued)
    (forward : Forward before after) : Identifies after worker issued := by
  refine ⟨Nat.lt_of_lt_of_le identity.1 forward.1, ?_⟩
  intro job member owner deadline running
  exact identity.2 job (forward.2 job member owner issued.attempt deadline running identity.1) owner deadline running

theorem initial : Valid ({} : State) := by
  constructor
  · intro job member worker attempt deadline running
    simp only [Array.mem_singleton] at member
    subst job
    cases running
  · intro first member second _ owner₁ owner₂ attempt deadline₁ deadline₂ running _
    simp only [Array.mem_singleton] at member
    subst first
    cases running

/-- A live report finds exactly its assigned job. The lookup cannot select a
different branch carrying the same attempt identity. -/
theorem live_report_selects (state : State) (report : Report) (job : Job) (deadline : Nat)
    (valid : Valid state) (member : job ∈ state.jobs)
    (running : job.status = .running report.worker report.attempt deadline) :
    ∃ index, state.jobs.findIdx? (fun job => match job.status with
      | .running worker attempt _ => worker == report.worker && attempt == report.attempt
      | _ => false) = some index ∧ state.jobs[index]! = job := by
  cases found : state.jobs.findIdx? (fun job => match job.status with
      | .running worker attempt _ => worker == report.worker && attempt == report.attempt
      | _ => false) with
  | none =>
    have absent := Array.findIdx?_eq_none_iff.mp found job member
    simp [running] at absent
  | some index =>
    obtain ⟨present, otherDeadline, selected⟩ := Scheduler.report_job state report index found
    exact ⟨index, rfl, valid.unique _ present job member _ _ _ _ _ selected running⟩

private def RunningSubset (before after : Array Job) : Prop :=
  ∀ job ∈ after, ∀ worker attempt deadline,
    job.status = .running worker attempt deadline → job ∈ before

private theorem RunningSubset.refl (jobs : Array Job) : RunningSubset jobs jobs :=
  fun _ member _ _ _ _ => member

private theorem RunningSubset.trans {first middle last}
    (earlier : RunningSubset first middle) (later : RunningSubset middle last) : RunningSubset first last :=
  fun job member worker attempt deadline running =>
    earlier job (later job member worker attempt deadline running) worker attempt deadline running

private theorem RunningSubset.valid {before after : State} (subset : RunningSubset before.jobs after.jobs)
    (counter : before.nextAttempt ≤ after.nextAttempt) (valid : Valid before) : Valid after := by
  constructor
  · intro job member worker attempt deadline running
    exact Nat.lt_of_lt_of_le (valid.bounded job (subset job member worker attempt deadline running)
      worker attempt deadline running) counter
  · intro first firstMember second secondMember owner₁ owner₂ attempt deadline₁ deadline₂ running₁ running₂
    exact valid.unique first (subset first firstMember owner₁ attempt deadline₁ running₁)
      second (subset second secondMember owner₂ attempt deadline₂ running₂)
      owner₁ owner₂ attempt deadline₁ deadline₂ running₁ running₂

private theorem RunningSubset.forward {before after : State} (subset : RunningSubset before.jobs after.jobs)
    (counter : before.nextAttempt ≤ after.nextAttempt) : Forward before after :=
  ⟨counter, fun job member worker attempt deadline running _ => subset job member worker attempt deadline running⟩

private theorem replace (jobs : Array Job) (index : Nat) (replacement : Job)
    (notRunning : ∀ worker attempt deadline, replacement.status ≠ .running worker attempt deadline) :
    RunningSubset jobs (jobs.set! index replacement) := by
  intro job member worker attempt deadline running
  rcases Array.mem_or_eq_of_mem_setIfInBounds member with member | same
  · exact member
  · subst job
    exact False.elim (notRunning worker attempt deadline running)

private theorem mapped (jobs : Array Job) (f : Job → Job)
    (unchanged : ∀ job worker attempt deadline, (f job).status = .running worker attempt deadline → f job = job) :
    RunningSubset jobs (jobs.map f) := by
  intro job member worker attempt deadline running
  obtain ⟨original, present, rfl⟩ := Array.mem_map.mp member
  simpa only [unchanged original worker attempt deadline running] using present

private theorem awaken_subset (state : State) : RunningSubset state.jobs (awaken state).jobs := by
  apply mapped
  intro job worker attempt deadline running
  cases status : job.status <;> simp_all
  split at running <;> simp_all

private theorem addChildren_subset (jobs : Array Job) (children : Array Location) :
    RunningSubset jobs (addChildren jobs children) := by
  apply Array.foldl_induction (fun _ current => RunningSubset jobs current) (.refl _)
  intro index current ih
  split
  · exact ih
  · intro job member worker attempt deadline running
    rcases Array.mem_push.mp member with member | same
    · exact ih job member worker attempt deadline running
    · subst job
      cases running

private theorem observe_counter (state : State) (worker : WorkerId) (keys : Array String) :
    (observe state worker keys).nextAttempt = state.nextAttempt := by
  simp [observe]
  split <;> rfl

private theorem observe_valid (state : State) (worker : WorkerId) (keys : Array String) (valid : Valid state) :
    Valid (observe state worker keys) := by
  apply RunningSubset.valid (before := state) ?_ ?_ valid
  · rw [Scheduler.observe_jobs]
    exact .refl _
  · simp only [observe_counter, Nat.le_refl]

private theorem observe_forward (state : State) (worker : WorkerId) (keys : Array String) :
    Forward state (observe state worker keys) := by
  apply RunningSubset.forward
  · rw [Scheduler.observe_jobs]
    exact .refl _
  · simp only [observe_counter, Nat.le_refl]

private theorem allocate (state : State) (index : Nat) (job : Job) (worker : WorkerId) (deadline : Nat)
    (valid : Valid state) :
    let fresh := { job with status := .running worker state.nextAttempt deadline }
    let after := { state with jobs := state.jobs.set! index fresh, nextAttempt := state.nextAttempt + 1 }
    Valid after ∧ Forward state after := by
  dsimp only
  constructor
  · constructor
    · intro current member owner attempt expires running
      rcases Array.mem_or_eq_of_mem_setIfInBounds member with member | same
      · exact Nat.lt_succ_of_lt (valid.bounded current member owner attempt expires running)
      · subst current
        cases running
        exact Nat.lt_succ_self _
    · intro first firstMember second secondMember owner₁ owner₂ attempt deadline₁ deadline₂ running₁ running₂
      rcases Array.mem_or_eq_of_mem_setIfInBounds firstMember with firstMember | rfl <;>
        rcases Array.mem_or_eq_of_mem_setIfInBounds secondMember with secondMember | rfl
      · exact valid.unique first firstMember second secondMember owner₁ owner₂ attempt deadline₁ deadline₂ running₁ running₂
      · cases running₂
        exact False.elim (Nat.lt_irrefl _ (valid.bounded first firstMember _ _ _ running₁))
      · cases running₁
        exact False.elim (Nat.lt_irrefl _ (valid.bounded second secondMember _ _ _ running₂))
      · rfl
  · refine ⟨Nat.le_succ _, ?_⟩
    intro current member owner attempt expires running old
    rcases Array.mem_or_eq_of_mem_setIfInBounds member with member | same
    · exact member
    · subst current
      cases running
      exact False.elim (Nat.lt_irrefl _ old)

/-- Assignment acquisition either resends an existing assignment unchanged or
allocates the next unused attempt number. -/
theorem acquire_preserves (state : State) (worker : WorkerId) (duration : Nat) (valid : Valid state) :
    Valid (acquire state worker duration).1 ∧ Forward state (acquire state worker duration).1 := by
  simp only [acquire]
  split
  · exact ⟨valid, .refl _⟩
  · split
    · exact ⟨valid, .refl _⟩
    · split
      · exact ⟨valid, .refl _⟩
      · split
        · exact allocate state _ _ worker _ valid
        · exact ⟨valid, .refl _⟩

private theorem accept_subset (state : State) (report : Report) :
    RunningSubset state.jobs (accept state report).jobs ∧ (accept state report).nextAttempt = state.nextAttempt := by
  simp only [accept, Scheduler.observe_jobs]
  split
  next index found =>
    cases progress : report.progress with
    | error error => exact ⟨.refl _, observe_counter ..⟩
    | ok result =>
      cases result with
      | done =>
        refine ⟨?_, observe_counter ..⟩
        exact (replace _ _ _ (by intros; simp)).trans (awaken_subset _)
      | fork location count =>
        refine ⟨?_, observe_counter ..⟩
        exact ((replace _ _ _ (by intros; simp)).trans (addChildren_subset _ _)).trans (awaken_subset _)
  next =>
    change RunningSubset state.jobs (observe state report.worker report.recorded).jobs ∧ _
    rw [Scheduler.observe_jobs]
    exact ⟨.refl _, observe_counter ..⟩

private theorem tick_subset (state : State) (duration elapsed : Nat) :
    RunningSubset state.jobs (handle duration state (.tick elapsed)).1.jobs := by
  apply mapped
  intro job worker attempt deadline running
  cases status : job.status with
  | pending | waiting _ | done => rfl
  | running owner attempt expires =>
    simp only [status] at running ⊢
    split at running
    · contradiction
    · rename_i unexpired
      simp [unexpired]

/-- Every scheduler message preserves unique live attempts and prevents reuse
of a historical attempt number, including arbitrary stale or duplicated reports. -/
theorem handle_preserves (state : State) (duration : Nat) (message : SchedulerMessage) (valid : Valid state) :
    Valid (handle duration state message).1 ∧ Forward state (handle duration state message).1 := by
  cases message with
  | ready worker =>
    obtain ⟨afterValid, forward⟩ := acquire_preserves (observe state worker #[]) worker duration (observe_valid _ _ _ valid)
    exact ⟨afterValid, (observe_forward _ _ _).trans forward⟩
  | report report =>
    obtain ⟨subset, counter⟩ := accept_subset state report
    exact ⟨subset.valid (Nat.le_of_eq counter.symm) valid, subset.forward (Nat.le_of_eq counter.symm)⟩
  | inspect replyTo => exact ⟨valid, .refl _⟩
  | tick elapsed =>
    have subset := tick_subset state duration elapsed
    exact ⟨subset.valid (Nat.le_refl _) valid, subset.forward (Nat.le_refl _)⟩

/-- Recovery keeps the allocation counter and releases old attempts. Delayed
messages can still refer to them, but subsequent acquisitions cannot reuse them. -/
theorem recover_preserves (state : State) (valid : Valid state) :
    Valid (Recovery.recovered state) ∧ Forward state (Recovery.recovered state) := by
  have subset : RunningSubset state.jobs (Recovery.recovered state).jobs := by
    intro job member worker attempt deadline running
    exact False.elim (Recovery.releases_assignments state job member worker attempt deadline running)
  exact ⟨subset.valid (Nat.le_refl _) valid, subset.forward (Nat.le_refl _)⟩

private theorem Valid.identifies {state : State} (valid : Valid state) (job : Job) (member : job ∈ state.jobs)
    (worker : WorkerId) (attempt deadline : Nat) (running : job.status = .running worker attempt deadline) :
    Identifies state worker (assignment job attempt) := by
  refine ⟨valid.bounded job member worker attempt deadline running, ?_⟩
  intro other otherMember owner expires otherRunning
  have same := valid.unique job member other otherMember worker owner attempt deadline expires running otherRunning
  subst other
  exact ⟨(Status.running.inj (otherRunning.symm.trans running)).1, rfl⟩

/-- Every returned assignment has the identity certified by the resulting
durable scheduler state. Repeated requests preserve the same certificate. -/
theorem acquire_identifies (state : State) (worker : WorkerId) (duration : Nat) (issued : Assignment)
    (valid : Valid state) (sent : (acquire state worker duration).2 = .execute issued) :
    Identifies (acquire state worker duration).1 worker issued := by
  cases error : state.error with
  | some errorValue => simp [acquire, error] at sent
  | none =>
    by_cases finished : state.finished = true
    · simp [acquire, error, finished] at sent
    · cases existing : state.jobs.findSome? (assignedTo worker) with
      | some old =>
        have same : old = issued := by simpa [acquire, error, finished, existing] using sent
        subst issued
        have after : (acquire state worker duration).1 = state := by simp [acquire, error, finished, existing]
        rw [after]
        obtain ⟨job, member, owned⟩ := Array.exists_of_findSome?_eq_some existing
        cases status : job.status with
        | pending | waiting _ | done => simp [assignedTo, status] at owned
        | running owner attempt deadline =>
          simp only [assignedTo, status] at owned
          split at owned
          · rename_i sameOwner
            have ownerEq : owner = worker := beq_iff_eq.mp sameOwner
            subst owner
            cases owned
            exact valid.identifies job member worker attempt deadline status
          · contradiction
      | none =>
        cases pending : state.jobs.findIdx? (fun job => job.status == .pending) with
        | none => simp [acquire, error, finished, existing, pending] at sent
        | some index =>
          have same : assignment state.jobs[index]! state.nextAttempt = issued := by
            simpa [acquire, error, finished, existing, pending] using sent
          subst issued
          obtain ⟨inside, _, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp pending
          have identity := (allocate state index state.jobs[index]! worker (state.now + max 1 duration) valid).1.identifies
            { state.jobs[index]! with status := .running worker state.nextAttempt (state.now + max 1 duration) }
            (Array.mem_setIfInBounds inside) worker state.nextAttempt (state.now + max 1 duration) rfl
          simpa only [acquire, error, finished, existing, pending, Bool.false_eq_true, ↓reduceIte] using! identity

/-- Every execute message emitted by the actual scheduler carries an assignment
whose identity survives subsequent scheduler transitions and restarts. -/
theorem handle_identifies (state : State) (duration : Nat) (message : SchedulerMessage) (valid : Valid state)
    (delivery : Delivery) (issued : Assignment)
    (sent : delivery ∈ (handle duration state message).2) (executes : delivery.message = .execute issued) :
    Identifies (handle duration state message).1 delivery.worker issued := by
  cases message with
  | ready worker =>
    change delivery ∈ #[⟨worker, (acquire (observe state worker #[]) worker duration).2⟩] at sent
    have same := Array.mem_singleton.mp sent
    subst delivery
    exact acquire_identifies (observe state worker #[]) worker duration issued (observe_valid _ _ _ valid) executes
  | report report =>
    simp only [handle, Array.mem_singleton] at sent
    subst delivery
    cases executes
  | inspect replyTo =>
    simp only [handle, Array.mem_singleton] at sent
    subst delivery
    cases executes
  | tick elapsed => simp [handle] at sent

end LeanCloud.Proofs.SchedulerAssignments
