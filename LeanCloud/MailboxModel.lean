import LeanCloud.Mailbox

namespace LeanCloud.MailboxModel

/-- Broker-owned state for one durable mailbox. Session numbers model new
consumer channels; delivery tags are never sufficient without that session. -/
structure Inbox (α : Type) where
  pending : Array α := #[]
  inFlight : Option (Received α) := none
  nextReceipt : Nat := 1
  session : Option Nat := none
  connected : Bool := false

private def requeue (inbox : Inbox α) : Inbox α :=
  match inbox.inFlight with
  | none => inbox
  | some delivery => { inbox with pending := #[delivery.message] ++ inbox.pending, inFlight := none }

def connect (generation : Nat) (inbox : Inbox α) : Inbox α :=
  if inbox.session.any (· ≥ generation) then inbox
  else { requeue inbox with session := some generation, connected := true }

/-- Closing a failed consumer never deletes its unacknowledged delivery. An old
connection close cannot disconnect a replacement consumer. -/
def disconnect (generation : Nat) (inbox : Inbox α) : Inbox α :=
  if inbox.session.any (· > generation) then inbox
  else { requeue inbox with session := some generation, connected := false }

def publish (message : α) (inbox : Inbox α) : Inbox α :=
  { inbox with pending := inbox.pending.push message }

def receive (generation : Nat) (inbox : Inbox α) : Option (Received α) × Inbox α :=
  if inbox.session != some generation || !inbox.connected || inbox.inFlight.isSome then (none, inbox)
  else match inbox.pending[0]? with
    | none => (none, inbox)
    | some message =>
      let delivery := { receipt := inbox.nextReceipt, message : Received α }
      let rest := inbox.pending.extract 1
      let after := { inbox with pending := rest, inFlight := some delivery, nextReceipt := inbox.nextReceipt + 1 }
      (some delivery, after)

def acknowledge (generation receipt : Nat) (inbox : Inbox α) : Inbox α :=
  if inbox.session == some generation && inbox.connected &&
      inbox.inFlight.any (fun delivery => delivery.receipt == receipt) then
    { inbox with inFlight := none }
  else inbox

end LeanCloud.MailboxModel
