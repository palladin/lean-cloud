import LeanCloud.MailboxModel

namespace LeanCloud.Proofs.Mailbox
open MailboxModel

/-- Messages still owned by the broker, including the reserved delivery. -/
def contents (inbox : Inbox α) : List α :=
  inbox.inFlight.toList.map (·.message) ++ inbox.pending.toList

/-- A confirmed publication adds one durable message. -/
theorem publish_appends (inbox : Inbox α) (message : α) :
    contents (publish message inbox) = contents inbox ++ [message] := by
  simp [contents, publish, List.append_assoc]

/-- A connected consumer with no outstanding delivery can receive the next
pending message. It stays reserved until that consumer acknowledges it. -/
theorem receive_next (inbox : Inbox α) (generation : Nat) (message : α)
    (session : inbox.session = some generation) (connected : inbox.connected = true)
    (available : inbox.inFlight = none) (next : inbox.pending[0]? = some message) :
    receive generation inbox =
      (some ⟨inbox.nextReceipt, message⟩,
        { inbox with pending := inbox.pending.extract 1, inFlight := some ⟨inbox.nextReceipt, message⟩, nextReceipt := inbox.nextReceipt + 1 }) := by
  simp [receive, session, connected, available, next]

/-- Receiving reserves a message without removing it from broker ownership. -/
theorem receive_preserves_messages (inbox : Inbox α) (generation : Nat) :
    contents (receive generation inbox).2 = contents inbox := by
  rcases inbox with ⟨⟨pending⟩, flight, receipt, session, connected⟩
  unfold receive
  split
  · rfl
  · cases flight with
    | some delivery => simp_all
    | none => cases pending <;> simp [contents, List.extract]

/-- Consumer failure preserves every message, including an unacknowledged one. -/
theorem disconnect_preserves_messages (inbox : Inbox α) (generation : Nat) :
    contents (disconnect generation inbox) = contents inbox := by
  rcases inbox with ⟨pending, flight, receipt, session, connected⟩
  unfold disconnect
  split
  · rfl
  · cases flight with
    | none => rfl
    | some delivery =>
      change (#[delivery.message] ++ pending).toList = delivery.message :: pending.toList
      simp

/-- Reconnecting changes ownership of the consumer session, not its messages. -/
theorem connect_preserves_messages (inbox : Inbox α) (generation : Nat) :
    contents (connect generation inbox) = contents inbox := by
  rcases inbox with ⟨pending, flight, receipt, session, connected⟩
  unfold connect
  split
  · rfl
  · cases flight with
    | none => rfl
    | some delivery =>
      change (#[delivery.message] ++ pending).toList = delivery.message :: pending.toList
      simp

/-- A late acknowledgement from an old process cannot remove anything. -/
theorem stale_acknowledgement_ignored (inbox : Inbox α) (generation receipt : Nat)
    (stale : inbox.session ≠ some generation) :
    acknowledge generation receipt inbox = inbox := by
  simp [acknowledge, stale]

/-- A valid acknowledgement removes precisely the reserved message. -/
theorem acknowledgement_removes_delivery (inbox : Inbox α) (generation : Nat)
    (delivery : Received α) (session : inbox.session = some generation)
    (connected : inbox.connected = true) (reserved : inbox.inFlight = some delivery) :
    contents inbox = delivery.message :: contents (acknowledge generation delivery.receipt inbox) := by
  simp [contents, acknowledge, session, connected, reserved]

/-- Every message retained by a durable mailbox satisfies the supplied
protocol property, including its unacknowledged delivery. -/
def All (property : α → Prop) (inbox : Inbox α) : Prop :=
  ∀ message ∈ contents inbox, property message

theorem All.empty (property : α → Prop) : All property {} := by
  simp [All, contents]

theorem All.mono {first second : α → Prop} {inbox : Inbox α} (valid : All first inbox)
    (implies : ∀ message, first message → second message) : All second inbox :=
  fun message member => implies message (valid message member)

theorem All.publish {property : α → Prop} {inbox : Inbox α} (valid : All property inbox)
    (message : α) (accepted : property message) : All property (MailboxModel.publish message inbox) := by
  intro value member
  rw [publish_appends] at member
  rcases List.mem_append.mp member with previous | added
  · exact valid value previous
  · simpa only [List.mem_singleton.mp added] using accepted

theorem All.receive {property : α → Prop} {inbox : Inbox α} (valid : All property inbox)
    (generation : Nat) : All property (MailboxModel.receive generation inbox).2 := by
  simpa only [All, receive_preserves_messages] using valid

theorem All.connect {property : α → Prop} {inbox : Inbox α} (valid : All property inbox)
    (generation : Nat) : All property (MailboxModel.connect generation inbox) := by
  simpa only [All, connect_preserves_messages] using valid

theorem All.disconnect {property : α → Prop} {inbox : Inbox α} (valid : All property inbox)
    (generation : Nat) : All property (MailboxModel.disconnect generation inbox) := by
  simpa only [All, disconnect_preserves_messages] using valid

theorem All.acknowledge {property : α → Prop} {inbox : Inbox α} (valid : All property inbox)
    (generation receipt : Nat) : All property (MailboxModel.acknowledge generation receipt inbox) := by
  unfold MailboxModel.acknowledge
  split
  · intro message member
    apply valid message
    exact List.mem_append_right _ member
  · exact valid

/-- Receiving cannot invent a message: the returned delivery satisfies every
property of the broker's retained messages. -/
theorem All.delivered {property : α → Prop} {inbox : Inbox α} (valid : All property inbox)
    (generation : Nat) (delivery : Received α) (received : (MailboxModel.receive generation inbox).1 = some delivery) :
    property delivery.message := by
  have reserved : (MailboxModel.receive generation inbox).2.inFlight = some delivery := by
    unfold MailboxModel.receive at received ⊢
    split at *
    · contradiction
    · split at *
      · contradiction
      · cases received
        simp_all
  apply valid.receive generation delivery.message
  simp [contents, reserved]

end LeanCloud.Proofs.Mailbox
