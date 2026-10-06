import LeanCloud.SourceInfo
import LeanCloud.Scheduler

namespace LeanCloud
open Lean

/-- Diagnostic state omits lease deadlines and records a parallel group's
size rather than its unbounded array of child locations. -/
inductive BranchStatus where
  | pending
  | running (worker : WorkerId) (attempt : Nat)
  | waiting (children : Nat)
  | done
  deriving BEq, Repr, Inhabited, ToJson, FromJson

structure BranchObservation where
  branch : Location
  location : Location
  joining : Bool
  status : BranchStatus
  deriving BEq, Repr, Inhabited, ToJson, FromJson

def BranchObservation.ofJob (job : Scheduler.Job) : BranchObservation :=
  { branch := job.branch, location := job.location, joining := job.joining
    status := match job.status with
      | .pending => .pending
      | .running worker attempt _ => .running worker attempt
      | .waiting children => .waiting children.size
      | .done => .done }

/-- Container counters sampled alongside an observation. Missing counters stay
missing. Monotonic time and incarnation fence rate calculations across restarts. -/
structure ResourceSample where
  incarnation : String
  timeNs : Nat
  cpuNs : Option Nat := none
  memory : Option Nat := none
  memoryLimit : Option Nat := none
  rx : Option Nat := none
  tx : Option Nat := none
  readBytes : Option Nat := none
  writeBytes : Option Nat := none
  diskUsed : Option Nat := none
  diskCapacity : Option Nat := none
  deriving ToJson, FromJson, Inhabited

/-- Best-effort observations, never an authority for execution or completion.
Sequence numbers are local to a worker incarnation, not a global clock. -/
structure ExecutionEvent where
  session : String
  seq : Nat
  elapsedMs : Nat
  worker : String
  attempt : Option Nat
  location : String
  activity : String
  operation : String
  run : String := ""
  source : Option SourceSiteId := none
  deriving ToJson, FromJson

end LeanCloud
