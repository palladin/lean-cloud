import LeanCloud.Location
import LeanCloud.Protocol

namespace LeanCloud

/-- What the environment currently offers to a worker. Idle is not completion. -/
inductive Work where
  | item (location : Location)
  | completed (outcome : Exit)
  | idle

/-- The selected item is replaced by its successors or the run's final outcome. -/
inductive StepResult where
  | runnable (locations : Array Location)
  | done (outcome : Exit)
  deriving Repr

/-- The environment owns work selection and persistence. Seed a new run with
`Location.root`; on restart, retain its queue and journal together.

`next` must leave the item recoverable until `complete` succeeds. `complete`
atomically replaces that item with successors, or records the final outcome.
The reference contract processes one item at a time; concurrent delivery and
leases are not specified here. The interpreter never reconstructs the queue.
Selection also requires the safety, retention, and fairness obligations in
`LeanCloud.Proofs.WorkQueue.Laws`; these are not implied by the monadic types. -/
structure WorkQueue (σ : Type) (m : Type → Type) where
  next : StateT σ m Work
  complete : Location → StepResult → StateT σ m Unit

end LeanCloud
