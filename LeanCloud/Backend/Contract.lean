import LeanCloud.Core
import LeanCloud.Location
import LeanCloud.Db

/-!
# Backend operation contracts

These are laws of individual service operations, independent of Cloud programs.
The state below is a specification/history, not a required database or queue
representation. In particular, queue publication identities and delivery receipts
are distinct from locations. Acknowledgement discharges a delivery obligation; it
does not promise that another copy can never arrive.
-/

namespace LeanCloud.Backend
open Lean

abbrev MessageId := Nat
abbrev Receipt := Nat

/-- A ghost checkpoint in the execution history, recorded by the specification. -/
structure DbSnapshot where
  records : List (String × Json) := []
  pastRecords : List (List (String × Json)) := []
  deriving Repr, BEq, Inhabited

structure Message where
  location : Location
  acknowledged : Bool := false
  published : DbSnapshot := {}
  deriving Repr, BEq, Inhabited

/-- Accepted publications remain in the history after acknowledgement. This
allows later duplicate deliveries without inventing a new publication. -/
structure QueueState where
  messages : Array Message := #[]
  receipts : Array MessageId := #[]
  deriving Repr, BEq

structure State where
  records : List (String × Json) := []
  /-- Ghost snapshots, newest first. The specification records committed writes;
  this is not an adapter API or a physical database log. -/
  pastRecords : List (List (String × Json)) := []
  queue : QueueState := {}
  deriving Repr, BEq

def State.snapshot (state : State) : DbSnapshot := ⟨state.records, state.pastRecords⟩

def DbSnapshot.state (snapshot : DbSnapshot) : State :=
  { records := snapshot.records, pastRecords := snapshot.pastRecords }

/-- The same operations exposed by Db and LeaseQueue, with typed replies.
Completion is an ordinary Db record; the queue has no completion operation. -/
inductive Request : Type → Type where
  | get (key : String) : Request (Option Json)
  | put (key : String) (value : Json) : Request Bool
  | enqueue (location : Location) : Request Unit
  | dequeue : Request (Option (Location × Receipt))
  | acknowledge (receipt : Receipt) : Request Bool

namespace Db

abbrev View := String → Option Json

def view (state : State) : View := fun key => state.records.lookup key

/-- A read observes the value at its linearization point. An older reply may
be delivered later; that does not turn a fresh read into an eventually-consistent
read. Changes to unrelated service state are excluded at this primitive boundary. -/
def Get (key : String) (before : State) (reply : Option Json) (after : State) : Prop :=
  reply = view before key ∧ after = before

/-- Raw writes need only support compatible journal writes. Pure workflow
proofs establish compatibility. A backend may reject a conflicting write; no
compare-and-set or multi-key transaction is required by this law. -/
def Compatible (key : String) (value : Json) (state : State) : Prop :=
  view state key = none ∨ view state key = some value

/-- The provider's observable write contract, without proof history. -/
def PutValue (key : String) (value : Json) (before : State) (reply : Bool) (after : State) : Prop :=
  if reply then
    view after key = some value ∧
    (∀ other, other ≠ key → view after other = view before other) ∧
    after.queue = before.queue
  else
    ¬ Compatible key value before ∧ after = before

def Put (key : String) (value : Json) (before : State) (reply : Bool) (after : State) : Prop :=
  if reply then
    view after key = some value ∧
    (∀ other, other ≠ key → view after other = view before other) ∧
    after.queue = before.queue ∧
    after.pastRecords = before.records :: before.pastRecords
  else
    ¬ Compatible key value before ∧ after = before

/-- Any observable atomic write can be recorded by the specification. The
snapshot clause therefore adds no requirement to a database adapter. -/
theorem record_put {key value before reply after} (law : PutValue key value before reply after) :
    Put key value before reply
      { after with pastRecords := if reply then before.records :: before.pastRecords else before.pastRecords } := by
  cases reply with
  | false =>
    obtain ⟨conflict, rfl⟩ := law
    exact ⟨conflict, rfl⟩
  | true =>
    obtain ⟨stored, unchanged, queue⟩ := law
    exact ⟨stored, unchanged, queue, rfl⟩

theorem Put.forget {key value before reply after} (law : Put key value before reply after) :
    PutValue key value before reply after := by
  cases reply with
  | false => exact law
  | true => exact ⟨law.1, law.2.1, law.2.2.1⟩

end Db

namespace Queue

def Enqueue (location : Location) (before : State) (reply : Unit) (after : State) : Prop :=
  reply = () ∧ after = { before with
    queue.messages := before.queue.messages.push { location, published := before.snapshot } }

/-- A receive may return idle, or any previously published payload, including
an acknowledged publication. There is no order or exclusive-lock promise.
Fresh model receipts distinguish deliveries even when their payloads agree. -/
def Dequeue (before : State) (reply : Option (Location × Receipt)) (after : State) : Prop :=
  match reply with
  | none => after = before
  | some (location, receipt) => ∃ id message,
    before.queue.messages[id]? = some message ∧ message.location = location ∧
    receipt = before.queue.receipts.size ∧
    after = { before with queue.receipts := before.queue.receipts.push id }

/-- Rejection changes nothing. Acceptance discharges the named publication's
obligation, but does not forbid future copies. Stale receipts need not be rejected.
The backend must never acknowledge an unrelated publication. -/
def Acknowledge (receipt : Receipt) (before : State) (reply : Bool) (after : State) : Prop :=
  if reply then ∃ id message,
    before.queue.receipts[receipt]? = some id ∧
    before.queue.messages[id]? = some message ∧
    after = { before with queue.messages := before.queue.messages.setIfInBounds id { message with acknowledged := true } }
  else after = before

end Queue

/-- One committed primitive. Failure and lost replies belong to the execution
history: neither is evidence that a request did not commit. -/
def Commits (before : State) : {α : Type} → Request α → α → State → Prop
  | _, .get key => Db.Get key before
  | _, .put key value => Db.Put key value before
  | _, .enqueue location => Queue.Enqueue location before
  | _, .dequeue => Queue.Dequeue before
  | _, .acknowledge receipt => Queue.Acknowledge receipt before

/-- A backend represents the specification state in any way it chooses.
These laws constrain individual committed operations, not their callers or the
workflow result. Auxiliary history may be included in the representation. -/
structure Laws (δ : Type) where
  view : δ → State
  operation : {α : Type} → Request α → δ → α → δ → Prop
  commits : ∀ {α} (request : Request α) before reply after,
    operation request before reply after → Commits (view before) request reply (view after)

end LeanCloud.Backend
