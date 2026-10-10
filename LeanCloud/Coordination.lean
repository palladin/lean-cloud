import LeanCloud.Location
import LeanCloud.Protocol

namespace LeanCloud
open Lean

/-- A stable actor address. A restarted worker reopens the same durable mailbox. -/
abbrev WorkerId := String

/-- A stable branch start and its current attempt. The worker discovers progress
from immutable records; assignments contain no replay cursor or join flag. -/
structure Assignment where
  attempt : Nat
  branchStart : Location
  deriving Repr, BEq, ToJson

/-- Old durable inbox messages may still contain a cursor. Keep their stable
branch identity and let replay discover progress from storage. -/
instance : FromJson Assignment where
  fromJson? json := do
    let branchStart ← match json.getObjVal? "branchStart" with
      | .ok value => fromJson? value
      | .error _ => json.getObjValAs? Location "branch"
    return { attempt := ← json.getObjValAs? Nat "attempt", branchStart }

/-- A worker reports control flow and record keys, never result values. -/
inductive Progress where
  | fork (location : Location) (count : Nat)
  | done
  deriving Repr, BEq, ToJson, FromJson

set_option linter.checkUnivs false in
deriving instance ToJson, FromJson for Except

structure Report where
  worker : WorkerId
  attempt : Nat
  progress : Except CloudError Progress
  recorded : Array String := #[]
  deriving Repr, ToJson, FromJson

/-- Durable inboxes retain confirmed requests and reports until acknowledged. Expiry
requests cancellation of abandoned assignments; stale attempts cannot satisfy replies. -/
inductive SchedulerMessage where
  | ready (worker : WorkerId)
  | stopped (worker : WorkerId) (barrier : Nat)
  | report (report : Report)
  | tick (elapsed : Nat)
  deriving Repr, ToJson, FromJson

inductive WorkerMessage where
  | execute (assignment : Assignment)
  | cancel (barrier : Nat)
  | acknowledged (attempt : Nat)
  | idle
  | finished
  | failed (error : CloudError)
  deriving Repr, ToJson, FromJson

structure Delivery where
  worker : WorkerId
  message : WorkerMessage
  deriving Repr, ToJson, FromJson

end LeanCloud
