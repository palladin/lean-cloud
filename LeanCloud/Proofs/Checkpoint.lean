import LeanCloud.Scheduler
import LeanCloud.Proofs.Location

namespace LeanCloud.Proofs

/-- A proof witness for the scheduler's last suspension. Only `work` is sent
to the worker; the replay interpreter never receives this cursor or join fact. -/
structure Checkpoint where
  attempt : Nat
  branch : Location
  location : Location
  joining : Bool := false

def Checkpoint.work (point : Checkpoint) : Assignment := ⟨point.attempt, point.branch⟩

instance : Coe Checkpoint Assignment := ⟨Checkpoint.work⟩

def Checkpoint.ofJob (job : Scheduler.Job) (attempt : Nat) : Checkpoint :=
  ⟨attempt, job.branch, job.location, job.joining⟩

end LeanCloud.Proofs
