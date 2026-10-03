import LeanCloud.Mailbox

namespace LeanCloud.Proofs.Recovery
open Scheduler

/-- The ideal private database. This runs the deployed recovery function against
ordinary state, rather than introducing another recovery implementation. -/
def database : SchedulerStore (StateM Scheduler.State) := ⟨get, set⟩

def recovered (state : Scheduler.State) : Scheduler.State :=
  ((Scheduler.recover database).run state).2

private theorem recovered_eq (state : Scheduler.State) :
    recovered state = { state with jobs := state.jobs.map fun job =>
      match job.status with
      | .running .. => { job with status := .pending }
      | _ => job } := rfl

/-- Repeated restarts cannot erase additional progress. -/
theorem idempotent (state : Scheduler.State) :
    recovered (recovered state) = recovered state := by
  cases state
  simp only [recovered_eq, Array.map_map, Scheduler.State.mk.injEq, and_true]
  apply Array.map_inj_left.mpr
  intro job _
  cases job with
  | mk branch location joining status => cases status <;> rfl

/-- Restart keeps the workflow's completion status. -/
theorem preserves_completion (state : Scheduler.State) :
    (recovered state).finished = state.finished := by
  rw [recovered_eq]
  change (state.jobs.map _).any _ = state.jobs.any _
  rw [Array.any_map]
  congr 1
  funext job
  cases job with
  | mk branch location joining status => cases status <;> rfl

/-- Restart changes assignment status, never branch identities, replay locations,
join modes, observed keys, attempt numbers, the clock, or a recorded error. -/
theorem preserves_metadata (state : Scheduler.State) :
    let after := recovered state
    after.jobs.map (fun job => (job.branch, job.location, job.joining)) =
      state.jobs.map (fun job => (job.branch, job.location, job.joining)) ∧
    after.workers = state.workers ∧ after.nextAttempt = state.nextAttempt ∧
    after.now = state.now ∧ after.error = state.error := by
  simp only [recovered_eq, Array.map_map, and_self, and_true]
  apply Array.map_inj_left.mpr
  intro job _
  cases job with
  | mk branch location joining status => cases status <;> rfl

/-- No assignment remains owned by a pre-restart attempt. -/
theorem releases_assignments (state : Scheduler.State) :
    ∀ job ∈ (recovered state).jobs, ∀ worker attempt deadline,
      job.status ≠ .running worker attempt deadline := by
  simp only [recovered_eq, Array.forall_mem_map]
  intro job _ worker attempt deadline
  cases job with
  | mk branch location joining status => cases status <;> simp

/-- Pending jobs, completed jobs, and partial joins survive unchanged. -/
theorem preserves_unassigned_jobs (state : Scheduler.State) (job : Job)
    (present : job ∈ state.jobs)
    (unassigned : ∀ worker attempt deadline, job.status ≠ .running worker attempt deadline) :
    job ∈ (recovered state).jobs := by
  rw [recovered_eq]
  apply Array.mem_map.mpr
  refine ⟨job, present, ?_⟩
  cases status : job.status with
  | pending | waiting _ | done => simp
  | running worker attempt deadline => exact False.elim (unassigned worker attempt deadline status)

end LeanCloud.Proofs.Recovery
