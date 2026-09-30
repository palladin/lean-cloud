import LeanCloud.LeaseQueueModel

/-! Local laws of the ideal leased queue. No fairness, concurrent-interpreter
safety, or refinement to a particular cloud service is claimed here. -/

namespace LeanCloud.Proofs.LeaseQueue
open LeaseQueueModel

theorem advance_retains_messages (state : State α) (elapsed : Nat) :
    (advance elapsed state).messages = state.messages := rfl

theorem lease_preserves_value (message : Message α) (now duration : Nat) :
    (message.lease now duration).value = message.value := rfl

/-- Slots are never reused. An existing live slot keeps its payload across
redelivery; it may become a tombstone. New payloads occupy new slots. -/
structure Lineage (before after : State α) : Prop where
  size : before.messages.size ≤ after.messages.size
  retained : ∀ (slot : Nat) (message : Message α), slot < before.messages.size →
    after.messages[slot]? = some (some message) →
    ∃ previous, before.messages[slot]? = some (some previous) ∧ previous.value = message.value

theorem Lineage.refl (state : State α) : Lineage state state :=
  ⟨Nat.le_refl _, fun _ message _ stored => ⟨message, stored, rfl⟩⟩

theorem Lineage.trans {before middle after : State α}
    (first : Lineage before middle) (last : Lineage middle after) : Lineage before after := by
  refine ⟨Nat.le_trans first.size last.size, ?_⟩
  intro slot message inside stored
  obtain ⟨intermediate, held, same⟩ := last.retained slot message (Nat.lt_of_lt_of_le inside first.size) stored
  obtain ⟨original, held, prior⟩ := first.retained slot intermediate inside held
  exact ⟨original, held, prior.trans same⟩

/-- An allocated slot cannot disappear by truncation or acquire another
payload: it is still live or has an acknowledgement tombstone. -/
theorem Lineage.live_or_removed {before after : State α} (lineage : Lineage before after)
    {slot : Nat} {message : Message α} (stored : before.messages[slot]? = some (some message)) :
    (∃ current, after.messages[slot]? = some (some current) ∧ current.value = message.value) ∨
      after.messages[slot]? = some none := by
  have inside := (Array.getElem?_eq_some_iff.mp stored).choose
  cases observed : after.messages[slot]? with
  | none =>
    have outside := Array.getElem?_eq_none_iff.mp observed
    have grows := lineage.size
    omega
  | some item =>
    cases item with
    | none => exact .inr rfl
    | some current =>
      obtain ⟨original, prior, same⟩ := lineage.retained slot current inside observed
      rw [stored] at prior
      cases prior
      exact .inl ⟨current, rfl, same.symm⟩

theorem Lineage.enqueue (state : State α) (value : α) :
    Lineage state (LeaseQueueModel.enqueue value state).2 := by
  refine ⟨by simp [LeaseQueueModel.enqueue], ?_⟩
  intro slot message inside stored
  simp only [LeaseQueueModel.enqueue, Array.getElem?_push, Nat.ne_of_lt inside, ↓reduceIte] at stored
  exact ⟨message, stored, rfl⟩

theorem Lineage.dequeue (state : State α) (duration : Nat) :
    Lineage state (LeaseQueueModel.dequeue duration state).2 := by
  unfold LeaseQueueModel.dequeue
  split
  · exact .refl _
  · rename_i selected found
    split
    · rename_i old occupied
      refine ⟨by simp, ?_⟩
      intro slot message inside stored
      by_cases same : selected = slot
      · subst slot
        simp only [Array.getElem?_setIfInBounds, inside, ↓reduceIte] at stored
        cases stored
        exact ⟨old, occupied, rfl⟩
      · simp only [Array.getElem?_setIfInBounds, same, ↓reduceIte] at stored
        exact ⟨message, stored, rfl⟩
    · exact .refl _

theorem Lineage.advance (state : State α) (elapsed : Nat) :
    Lineage state (LeaseQueueModel.advance elapsed state) :=
  ⟨Nat.le_refl _, fun _ message _ stored => ⟨message, stored, rfl⟩⟩

/-- Every retained payload satisfies a property, whether visible or leased. -/
def Values (property : α → Prop) (state : State α) : Prop :=
  ∀ (index : Nat) (message : Message α), state.messages[index]? = some (some message) → property message.value

theorem Values.enqueue {property : α → Prop} {state : State α} {value : α}
    (valid : Values property state) (allowed : property value) :
    Values property (LeaseQueueModel.enqueue value state).2 := by
  intro index message stored
  simp only [LeaseQueueModel.enqueue, Array.getElem?_push] at stored
  split at stored
  · cases stored; exact allowed
  · exact valid index message stored

theorem Values.dequeue {property : α → Prop} {state : State α}
    (valid : Values property state) (duration : Nat) :
    Values property (LeaseQueueModel.dequeue duration state).2 ∧
      ∀ delivery, (LeaseQueueModel.dequeue duration state).1 = some delivery → property delivery.value := by
  unfold LeaseQueueModel.dequeue
  split
  · exact ⟨valid, by intro delivery impossible; cases impossible⟩
  · rename_i selected found
    split
    · rename_i old slot
      constructor
      · intro index message stored
        by_cases same : selected = index
        · subst index
          have inside := (Array.getElem?_eq_some_iff.mp slot).choose
          simp only [Array.getElem?_setIfInBounds, inside, ↓reduceIte] at stored
          cases stored
          exact valid selected old slot
        · simp only [Array.getElem?_setIfInBounds, same, ↓reduceIte] at stored
          exact valid index message stored
      · intro delivery returned
        cases returned
        exact valid selected old slot
    · exact ⟨valid, by intro delivery impossible; cases impossible⟩

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

theorem Lineage.acknowledge (state : State α) (receipt : Receipt) :
    Lineage state (LeaseQueueModel.acknowledge receipt state).2 := by
  cases observed : current receipt state with
  | none => simpa only [LeaseQueueModel.acknowledge, observed] using Lineage.refl state
  | some old =>
    refine ⟨by simp [LeaseQueueModel.acknowledge, observed], ?_⟩
    intro slot message inside stored
    by_cases same : receipt.message = slot
    · subst slot
      rw [acknowledge_removes observed] at stored
      cases stored
    · exact ⟨message, (acknowledge_preserves_other receipt state slot same).symm.trans stored, rfl⟩

theorem Values.acknowledge {property : α → Prop} {state : State α}
    (valid : Values property state) (receipt : Receipt) :
    Values property (LeaseQueueModel.acknowledge receipt state).2 := by
  cases read : current receipt state with
  | none => simpa only [LeaseQueueModel.acknowledge, read] using valid
  | some old =>
    intro index message stored
    by_cases same : receipt.message = index
    · subst index
      rw [acknowledge_removes read] at stored
      cases stored
    · exact valid index message ((acknowledge_preserves_other receipt state index same).symm.trans stored)

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
