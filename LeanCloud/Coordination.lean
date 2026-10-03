import LeanCloud.Location
import LeanCloud.Protocol

namespace LeanCloud
open Lean

/-- A stable actor address. A restarted worker reopens the same durable mailbox. -/
abbrev WorkerId := String

/-- Reconstruct the root program at `location`. `branch` identifies the stable
completion key. `joining` authorizes reading the now-complete child records. -/
structure Assignment where
  attempt : Nat
  branch : Location
  location : Location
  joining : Bool := false
  deriving Repr, BEq, ToJson, FromJson

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

/-- RabbitMQ retains confirmed requests and reports until acknowledged. Expiry
makes abandoned assignments available again; stale attempts cannot change jobs. -/
inductive SchedulerMessage where
  | ready (worker : WorkerId)
  | report (report : Report)
  | tick (elapsed : Nat)
  | inspect (replyTo : WorkerId)
  deriving Repr, ToJson, FromJson

inductive WorkerMessage where
  | execute (assignment : Assignment)
  | acknowledged (attempt : Nat)
  | idle
  | finished
  | failed (error : CloudError)
  | status (metadata : Json)
  deriving Repr, ToJson, FromJson

structure Delivery where
  worker : WorkerId
  message : WorkerMessage
  deriving Repr, ToJson, FromJson

end LeanCloud
