import LeanCloud.Location
import LeanCloud.Protocol

namespace LeanCloud

/-- What the environment currently offers to a worker. Idle is not completion. -/
inductive Work where
  | item (location : Location)
  | completed (outcome : Exit)
  | idle

/-- Work to publish before acknowledging the selected item. -/
inductive StepResult where
  | runnable (locations : Array Location)
  | done (outcome : Exit)
  deriving Repr

/-- The environment owns work selection and persistence. Seed a new run with
`Location.root`; on restart, retain its queue and journal together.

`next` must leave the item recoverable until it is acknowledged. `complete`
publishes successors (or the final result) before acknowledging the delivery.
These operations can be interrupted separately; retries may publish duplicates.
Call `complete` for the item returned by this worker's most recent `next`.

The ideal reference backend combines publication and acknowledgement atomically.
The lease adapter separates them. The equivalence theorem's stronger
`LeanCloud.Proofs.QueueContract`, and its fairness assumptions, are additional
obligations; they are not implied by this interface or satisfied automatically
by leased transport. The ideal logical Db assumes serialized workers; `JournalDb`
provides separate physical child records, with its own same-value writer
assumption. Full concurrent-worker correctness is a separate proof obligation. -/
structure WorkQueue (σ : Type) (m : Type → Type) where
  next : StateT σ m Work
  complete : Location → StepResult → StateT σ m Unit

end LeanCloud
