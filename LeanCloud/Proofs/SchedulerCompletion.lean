import LeanCloud.Proofs.SchedulerProgress

/-! Completed jobs survive every scheduler transition. This monotone part of
coordination state is independent of assignment expiry and report redelivery. -/

namespace LeanCloud.Proofs.SchedulerCompletion
open LeanCloud.Scheduler Internal

def Preserves (before after : Array Job) : Prop :=
  ∀ job ∈ before, job.status = .done → job ∈ after

theorem Preserves.refl (jobs : Array Job) : Preserves jobs jobs := fun _ member _ => member

theorem Preserves.trans {first middle last : Array Job}
    (earlier : Preserves first middle) (later : Preserves middle last) : Preserves first last :=
  fun job member done => later job (earlier job member done) done

theorem Preserves.done {before after : Array Job} (keeps : Preserves before after) {branch : Location}
    (completed : SchedulerProgress.Done before branch) : SchedulerProgress.Done after branch := by
  obtain ⟨job, member, same, done⟩ := completed
  exact ⟨job, keeps job member done, same, done⟩

private theorem mapped (jobs : Array Job) (f : Job → Job)
    (unchanged : ∀ job ∈ jobs, job.status = .done → f job = job) : Preserves jobs (jobs.map f) :=
  fun job member done => Array.mem_map.mpr ⟨job, member, unchanged job member done⟩

private theorem replace (jobs : Array Job) (index : Nat) (replacement : Job)
    (unfinished : jobs[index]!.status ≠ .done) : Preserves jobs (jobs.set! index replacement) := by
  intro job member done
  obtain ⟨position, inside, same⟩ := Array.mem_iff_getElem.mp member
  have different : index ≠ position := by
    intro equal
    subst index
    exact unfinished (by simpa [getElem!_pos jobs position inside, same] using done)
  change job ∈ jobs.setIfInBounds index replacement
  apply Array.mem_iff_getElem.mpr
  refine ⟨position, by simpa using inside, ?_⟩
  simpa [Array.getElem_setIfInBounds inside, different] using same

private theorem awaken (state : State) : Preserves state.jobs (Internal.awaken state).jobs :=
  mapped state.jobs _ (fun job _ done => by simp [done])

private theorem addChildren (jobs : Array Job) (children : Array Location) :
    Preserves jobs (Internal.addChildren jobs children) := by
  apply Array.foldl_induction (fun _ current => Preserves jobs current) (.refl _)
  intro index current ih
  split
  · exact ih
  · exact fun job member done => Array.mem_push.mpr (Or.inl (ih job member done))

theorem acquire (state : State) (worker : WorkerId) (duration : Nat) :
    Preserves state.jobs (Internal.acquire state worker duration).1.jobs := by
  simp only [Internal.acquire]
  split
  · exact .refl _
  · split
    · exact .refl _
    · split
      · exact .refl _
      · split
        next index found =>
          obtain ⟨inside, selected, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp found
          apply replace
          intro done
          rw [getElem!_pos state.jobs index inside] at done
          rw [done] at selected
          contradiction
        next => exact .refl _

theorem accept (state : State) (report : Report) : Preserves state.jobs (Internal.accept state report).jobs := by
  simp only [Internal.accept, Scheduler.observe_jobs]
  split
  next index found =>
    obtain ⟨_, deadline, running⟩ := Scheduler.report_job state report index found
    have unfinished : state.jobs[index]!.status ≠ .done := by simp [running]
    cases report.progress with
    | error _ => exact .refl _
    | ok progress =>
      cases progress with
      | done =>
        dsimp only [Id.run, pure]
        apply Preserves.trans (later := awaken _)
        exact replace _ _ _ unfinished
      | fork location count =>
        dsimp only [Id.run, pure]
        apply Preserves.trans (later := awaken _)
        apply Preserves.trans (later := addChildren _ _)
        exact replace _ _ _ unfinished
  next => simpa only [Id.run, pure, Scheduler.observe_jobs] using! Preserves.refl state.jobs

/-- No message can undo a completed job, including expiry ticks, duplicate
reports, reports for other branches, and requests for more work. -/
theorem handle (state : State) (duration : Nat) (message : SchedulerMessage) :
    Preserves state.jobs (Scheduler.handle duration state message).1.jobs := by
  cases message with
  | ready worker =>
    simpa only [Scheduler.observe_jobs] using! acquire (observe state worker #[]) worker duration
  | report report => exact accept state report
  | inspect _ => exact .refl _
  | tick elapsed => exact mapped _ _ (fun job _ done => by simp [done])

theorem recover (state : State) : Preserves state.jobs (Recovery.recovered state).jobs := by
  intro job member done
  apply Recovery.preserves_unassigned_jobs state job member
  intros
  simp [done]

/-- Workflow completion, once saved, remains true under every scheduler
message and recovery. The root job itself survives unchanged. -/
theorem Preserves.finished {before after : State} (keeps : Preserves before.jobs after.jobs)
    (finished : before.finished = true) : after.finished = true := by
  obtain ⟨job, member, matched⟩ := Array.any_eq_true'.mp finished
  have parts : job.branch = Location.root ∧ job.status = .done := by
    simpa only [Bool.and_eq_true, beq_iff_eq, Scheduler.done_iff] using matched
  obtain ⟨root, done⟩ := parts
  exact Array.any_eq_true'.mpr ⟨job, keeps job member done, by simp [root, done, Scheduler.done_iff]⟩

end LeanCloud.Proofs.SchedulerCompletion
