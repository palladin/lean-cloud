import LeanCloud.LeaseQueueModel

/-! Local laws of the ideal leased queue. No fairness, concurrent-interpreter
safety, or refinement to a particular cloud service is claimed here. -/

namespace LeanCloud.Proofs.LeaseQueue
open LeaseQueueModel

theorem advance_retains_messages (state : State α) (elapsed : Nat) :
    (advance elapsed state).messages = state.messages := rfl

theorem lease_preserves_value (message : Message α) (now duration : Nat) :
    (message.lease now duration).value = message.value := rfl

theorem lease_hidden (message : Message α) (now duration elapsed : Nat)
    (beforeExpiry : elapsed < duration) :
    (message.lease now duration).visible (now + elapsed) = false := by
  simp [Message.lease, Message.visible, show ¬ now + duration ≤ now + elapsed by omega]

theorem lease_expires (message : Message α) (now duration elapsed : Nat)
    (expired : duration ≤ elapsed) :
    (message.lease now duration).visible (now + elapsed) = true := by
  simp [Message.lease, Message.visible, show now + duration ≤ now + elapsed by omega]

theorem current_iff {receipt : Receipt} {state : State α} {message : Message α} :
    current receipt state = some message ↔
      state.messages[receipt.message]? = some (some message) ∧
      receipt.generation ≠ 0 ∧ receipt.generation = message.generation := by
  unfold current
  cases slot : state.messages[receipt.message]? with
  | none => simp
  | some item =>
    cases item with
    | none => simp
    | some item =>
      split <;> simp_all <;> grind

theorem invalid_acknowledge (receipt : Receipt) (state : State α)
    (invalid : current receipt state = none) :
    acknowledge receipt state = (false, state) := by
  simp [acknowledge, invalid]

theorem acknowledge_removes {receipt : Receipt} {state : State α} {message : Message α}
    (valid : current receipt state = some message) :
    (acknowledge receipt state).2.messages[receipt.message]? = some none := by
  have slot := (current_iff.mp valid).1
  obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp slot
  simp [acknowledge, valid, inside]

theorem acknowledge_preserves_other (receipt : Receipt) (state : State α) (index : Nat)
    (other : receipt.message ≠ index) :
    (acknowledge receipt state).2.messages[index]? = state.messages[index]? := by
  cases valid : current receipt state <;> simp [acknowledge, valid, other]

/-- A successful dequeue leaves the leased payload in the queue, accessible by
its returned receipt. The worker receiving it is not a deletion event. -/
theorem dequeue_retains {state next : State α} {duration : Nat} {delivery : Delivery α}
    (returned : dequeue duration state = (some delivery, next)) :
    ∃ message, current delivery.receipt next = some message ∧
      message.value = delivery.value ∧ message.visibleAt = delivery.visibleAt := by
  unfold dequeue at returned
  split at returned
  · cases returned
  · rename_i index selected
    split at returned
    · rename_i message slot
      have inside := (Array.getElem?_eq_some_iff.mp slot).choose
      simp only [Prod.mk.injEq, Option.some.injEq] at returned
      rcases returned with ⟨rfl, rfl⟩
      refine ⟨message.lease state.now duration, ?_, rfl, rfl⟩
      apply current_iff.mpr
      simp [inside, Message.lease]
    · cases returned

/-- Renewal changes the receipt. An old worker cannot use the earlier receipt
to delete the renewed delivery in this ideal model. -/
theorem renew_invalidates_old {receipt : Receipt} {state : State α} {message : Message α}
    (valid : current receipt state = some message) (duration : Nat) :
    current receipt (renew receipt duration state).2 = none := by
  obtain ⟨slot, _, generation⟩ := current_iff.mp valid
  obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp slot
  unfold renew
  rw [valid]
  simp [current, inside, Message.lease, generation]

end LeanCloud.Proofs.LeaseQueue
