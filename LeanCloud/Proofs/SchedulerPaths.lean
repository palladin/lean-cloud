import LeanCloud.Proofs.Scheduler
import LeanCloud.Proofs.Suspension

namespace LeanCloud.Proofs.SchedulerPaths
open Lean LeanCloud.Scheduler Internal ReplayModel Reconstruction

/-- Every durable job location can be reconstructed from the original workflow. -/
def Valid {m : Type → Type u} (journal : Journal) (encode : α → Json) (program : Cloud m α) (jobs : Array Job) : Prop :=
  ∀ job ∈ jobs, Resumable journal encode program Location.root job.location

variable {m : Type → Type u} {encode : α → Json} {program : Cloud m α}

theorem Valid.extend {before after jobs} (valid : Valid before encode program jobs) (extension : Extends before after) :
    Valid after encode program jobs := fun job member => (valid job member).extend extension

theorem initial (journal : Journal) (encode : α → Json) (program : Cloud m α) :
    Valid journal encode program ({} : State).jobs := by
  intro job member
  simp only [Array.mem_singleton] at member
  subst job
  exact .here ..

private theorem replace {journal jobs} (valid : Valid journal encode program jobs) (index : Nat) (replacement : Job)
    (resumable : Resumable journal encode program Location.root replacement.location) :
    Valid journal encode program (jobs.set! index replacement) := by
  intro job member
  rcases Array.mem_or_eq_of_mem_setIfInBounds member with member | same
  · exact valid job member
  · subst job; exact resumable

private theorem mapped {journal jobs} (valid : Valid journal encode program jobs) (f : Job → Job)
    (preserves : ∀ job, (f job).location = job.location) : Valid journal encode program (jobs.map f) := by
  intro job member
  obtain ⟨original, present, rfl⟩ := Array.mem_map.mp member
  simpa only [preserves original] using valid original present

theorem awaken_preserves (state : State) (journal : Journal) (valid : Valid journal encode program state.jobs) :
    Valid journal encode program (awaken state).jobs := by
  apply mapped valid
  intro job
  cases job.status <;> simp_all
  split <;> rfl

theorem addChildren_preserves (journal : Journal) (jobs : Array Job) (children : Array Location)
    (valid : Valid journal encode program jobs)
    (paths : ∀ child ∈ children, Resumable journal encode program Location.root child) :
    Valid journal encode program (addChildren jobs children) := by
  apply Array.foldl_induction (fun _ current => Valid journal encode program current) valid
  intro index current ih
  split
  · exact ih
  · intro job member
    rcases Array.mem_push.mp member with member | same
    · exact ih job member
    · subst job
      exact paths _ (Array.getElem_mem _)

theorem acquire_preserves (state : State) (journal : Journal) (worker : WorkerId) (duration : Nat)
    (valid : Valid journal encode program state.jobs) : Valid journal encode program (acquire state worker duration).1.jobs := by
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
          apply replace valid
          apply valid (state.jobs[index]!)
          rw [getElem!_pos state.jobs index inside]
          exact Array.getElem_mem inside
        next => exact valid

/-- A fork report supplies both the parent's new replay path and the paths of
new child jobs. Repeated or stale reports cannot invalidate existing paths. -/
theorem accept_preserves (state : State) (journal : Journal) (report : Report)
    (valid : Valid journal encode program state.jobs) (paths : Suspension.ReportPaths journal encode program report) :
    Valid journal encode program (accept state report).jobs := by
  simp only [accept, Scheduler.observe_jobs]
  split
  next index found =>
    obtain ⟨member, _, _⟩ := Scheduler.report_job state report index found
    cases progress : report.progress with
    | error error => exact valid
    | ok result =>
      cases result with
      | done =>
        apply awaken_preserves
        exact replace valid index _ (valid (state.jobs[index]!) member)
      | fork location count =>
        have certified := paths location count progress
        apply awaken_preserves
        apply addChildren_preserves
        · exact replace valid index _ certified.1
        · intro child member
          obtain ⟨index, inside, rfl⟩ := Array.mem_map.mp member
          exact certified.2 ⟨index, Array.mem_range.mp inside⟩
  next =>
    change Valid journal encode program (observe state report.worker report.recorded).jobs
    simpa only [Scheduler.observe_jobs] using valid

theorem tick_preserves (state : State) (journal : Journal) (duration elapsed : Nat)
    (valid : Valid journal encode program state.jobs) :
    Valid journal encode program (handle duration state (.tick elapsed)).1.jobs := by
  apply mapped valid
  intro job
  cases job.status <;> simp_all
  split <;> rfl

theorem recover_preserves (state : State) (journal : Journal) (valid : Valid journal encode program state.jobs) :
    Valid journal encode program (Recovery.recovered state).jobs := by
  apply mapped valid
  intro job
  cases job.status <;> rfl

theorem handle_preserves (state : State) (journal : Journal) (duration : Nat) (message : SchedulerMessage)
    (valid : Valid journal encode program state.jobs)
    (paths : match message with | .report report => Suspension.ReportPaths journal encode program report | _ => True) :
    Valid journal encode program (handle duration state message).1.jobs := by
  cases message with
  | ready worker =>
    apply acquire_preserves
    simpa only [Scheduler.observe_jobs] using valid
  | report report => exact accept_preserves state journal report valid paths
  | inspect replyTo => exact valid
  | tick elapsed => exact tick_preserves state journal duration elapsed valid

/-- Every emitted assignment has a path from the original workflow. -/
theorem handle_resumable (state : State) (journal : Journal) (duration : Nat) (message : SchedulerMessage)
    (valid : Valid journal encode program state.jobs) (delivery : Delivery) (issued : Assignment)
    (sent : delivery ∈ (handle duration state message).2) (executes : delivery.message = .execute issued) :
    Resumable journal encode program Location.root issued.location := by
  obtain ⟨job, member, attempt, rfl⟩ := Scheduler.handle_from_job state duration message delivery issued sent executes
  exact valid job member

end LeanCloud.Proofs.SchedulerPaths
