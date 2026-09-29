import Lean

/-! An ideal queue with explicit time and receipt-based acknowledgement.
Each operation is one pure state transition, suitable for `CrashModel.atomic`.
`LeaseQueue.toWorkQueue` connects these primitives to replay, separating
successor publication from acknowledgement.

Time belongs to the environment. A worker crash neither advances time nor
releases its delivery. Dequeue and renewal rotate the receipt; expiry alone
allows redelivery but does not invalidate the current receipt. This ideal model
rejects stale receipts. A cloud adapter must account for its service's weaker
delivery/deletion guarantees; the model is not a distributed execution lock. -/

namespace LeanCloud.LeaseQueueModel

structure Receipt where
  message : Nat
  generation : Nat
  deriving Repr, BEq, DecidableEq

structure Delivery (α : Type) where
  value : α
  receipt : Receipt
  visibleAt : Nat
  deriving Repr, BEq

structure Message (α : Type) where
  value : α
  generation : Nat := 0
  visibleAt : Nat := 0
  deriving Repr, BEq

/-- Slots are never reused, including after acknowledgement. Equal payloads can
occupy different slots and must be acknowledged separately. -/
structure State (α : Type) where
  now : Nat := 0
  messages : Array (Option (Message α)) := #[]
  deriving Repr, BEq

def Message.visible (message : Message α) (now : Nat) : Bool := message.visibleAt ≤ now

def Message.lease (message : Message α) (now duration : Nat) : Message α :=
  { message with generation := message.generation + 1, visibleAt := now + duration }

/-- Enqueue always inserts a distinct message. Retrying an enqueue whose reply
was lost can produce duplicate work; no implicit deduplication is assumed. -/
def enqueue (value : α) (state : State α) : Nat × State α :=
  (state.messages.size, { state with messages := state.messages.push (some ⟨value, 0, state.now⟩) })

/-- The first visible slot is this model's selection policy, not a FIFO promise
for real queues. A zero duration permits immediate redelivery. -/
def dequeue (duration : Nat) (state : State α) : Option (Delivery α) × State α :=
  match state.messages.findIdx? (fun item => item.any (·.visible state.now)) with
  | none => (none, state)
  | some index =>
    match state.messages[index]? with
    | some (some message) =>
      let message := message.lease state.now duration
      let delivery : Delivery α := {
        value := message.value
        receipt := ⟨index, message.generation⟩
        visibleAt := message.visibleAt }
      (some delivery, { state with messages := state.messages.setIfInBounds index (some message) })
    | _ => (none, state)

/-- A receipt authorizes its current delivery, even after expiry if no new
delivery has replaced it. Generation zero has never been handed to a worker. -/
def current (receipt : Receipt) (state : State α) : Option (Message α) :=
  match state.messages[receipt.message]? with
  | some (some message) =>
    if receipt.generation ≠ 0 && receipt.generation == message.generation then
      some message
    else none
  | _ => none

def acknowledge (receipt : Receipt) (state : State α) : Bool × State α :=
  match current receipt state with
  | none => (false, state)
  | some _ => (true, { state with messages := state.messages.setIfInBounds receipt.message none })

/-- Renewal sets visibility relative to the current time and returns a new
receipt. Losing that reply leaves the renewed lease in place until expiry. -/
def renew (receipt : Receipt) (duration : Nat) (state : State α) :
    Option (Delivery α) × State α :=
  match current receipt state with
  | none => (none, state)
  | some message =>
    let message := message.lease state.now duration
    let delivery : Delivery α := {
      value := message.value
      receipt := ⟨receipt.message, message.generation⟩
      visibleAt := message.visibleAt }
    (some delivery, { state with messages := state.messages.setIfInBounds receipt.message (some message) })

/-- Time passing is explicit and never drops messages. In particular, an idle
poll or a caught crash does not secretly expire a lease. -/
def advance (elapsed : Nat) (state : State α) : State α :=
  { state with now := state.now + elapsed }

end LeanCloud.LeaseQueueModel
