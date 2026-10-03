import LeanCloud.Backend.Contract

namespace LeanCloud.Backend.Proofs

/-- Publication identities are never reused, their payload and publication
checkpoint never change, and delivery receipts retain their referent. -/
structure QueueLineage (before after : QueueState) : Prop where
  size : before.messages.size ≤ after.messages.size
  messages : ∀ (id : Nat) (old : Backend.Message), before.messages[id]? = some old →
    ∃ current, after.messages[id]? = some current ∧ current.location = old.location ∧
      current.published = old.published ∧ (old.acknowledged = true → current.acknowledged = true)
  receipts : ∀ (receipt : Nat) (id : MessageId), before.receipts[receipt]? = some id →
    after.receipts[receipt]? = some id

theorem QueueLineage.refl (state : QueueState) : QueueLineage state state :=
  ⟨Nat.le_refl _, fun _ message stored => ⟨message, stored, rfl, rfl, id⟩, fun _ _ stored => stored⟩

theorem QueueLineage.trans {first middle last : QueueState}
    (a : QueueLineage first middle) (b : QueueLineage middle last) : QueueLineage first last := by
  refine ⟨Nat.le_trans a.size b.size, ?_, fun receipt message stored => b.receipts receipt message (a.receipts receipt message stored)⟩
  intro id message stored
  obtain ⟨second, held, location, published, acknowledged⟩ := a.messages id message stored
  obtain ⟨third, found, nextLocation, nextPublished, nextAck⟩ := b.messages id second held
  exact ⟨third, found, nextLocation.trans location, nextPublished.trans published, fun ack => nextAck (acknowledged ack)⟩

theorem QueueLineage.enqueue (state : QueueState) (message : Backend.Message) :
    QueueLineage state { state with messages := state.messages.push message } := by
  refine ⟨by simp, ?_, fun _ _ stored => stored⟩
  intro id old stored
  have inside := (Array.getElem?_eq_some_iff.mp stored).choose
  exact ⟨old, by simpa [Array.getElem?_push, Nat.ne_of_lt inside] using stored, rfl, rfl, fun ack => ack⟩

theorem QueueLineage.receive (state : QueueState) (id : MessageId) :
    QueueLineage state { state with receipts := state.receipts.push id } := by
  refine ⟨Nat.le_refl _, fun _ message stored => ⟨message, stored, rfl, rfl, fun ack => ack⟩, ?_⟩
  intro receipt message stored
  have inside := (Array.getElem?_eq_some_iff.mp stored).choose
  simpa [Array.getElem?_push, Nat.ne_of_lt inside] using stored

theorem QueueLineage.acknowledge (state : QueueState) (id : MessageId) (message : Backend.Message)
    (stored : state.messages[id]? = some message) :
    QueueLineage state { state with messages := state.messages.setIfInBounds id { message with acknowledged := true } } := by
  refine ⟨by simp, ?_, fun _ _ stored => stored⟩
  intro other old found
  by_cases same : other = id
  · subst other
    have equal := Option.some.inj (found.symm.trans stored)
    subst old
    have inside := (Array.getElem?_eq_some_iff.mp stored).choose
    exact ⟨{ message with acknowledged := true }, by simp [inside], rfl, rfl, fun _ => rfl⟩
  · exact ⟨old, by simp [Ne.symm same, found], rfl, rfl, fun ack => ack⟩

/-- These lineage laws follow from primitive queue contracts alone. -/
theorem commits_lineage {α : Type} {operation : Request α} {before after value}
    (law : Commits before operation value after) : QueueLineage before.queue after.queue := by
  cases operation with
  | get key => obtain ⟨_, rfl⟩ := law; exact .refl _
  | put key stored =>
    cases value with
    | false => obtain ⟨_, rfl⟩ := law; exact .refl _
    | true => rw [law.2.2.1]; exact .refl _
  | enqueue location => obtain ⟨rfl, rfl⟩ := law; exact .enqueue _ _
  | dequeue =>
    cases value with
    | none => have same : after = before := law; subst after; exact .refl _
    | some pair =>
      obtain ⟨location, receipt⟩ := pair
      obtain ⟨id, message, stored, rfl, rfl, rfl⟩ := law
      exact .receive _ _
  | acknowledge receipt =>
    cases value with
    | false => have same : after = before := law; subst after; exact .refl _
    | true =>
      obtain ⟨id, message, known, stored, rfl⟩ := law
      exact .acknowledge _ _ _ stored

end LeanCloud.Backend.Proofs
