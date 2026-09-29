import LeanCloud.Proofs.TreeSuccessors
import LeanCloud.Proofs.LeasePublication

/-! The worker's program-derived responses remain valid through the actual
lease adapter, including partially committed successor publication. -/

namespace LeanCloud.Proofs.LeasePublication
open Lean CrashModel LeaseQueueModel CrashRecovery

/-- A transport predicate for both visible and leased messages, together with
the intended final outcome. Lease changes do not alter a message's payload. -/
def QueueValid (allowed : Location → Prop) (expected : Exit) (state : Durable) : Prop :=
  (∀ message, some message ∈ state.transport.messages → allowed message.value) ∧
    ∀ outcome, state.completed = some outcome → outcome = expected

theorem QueueValid.empty (allowed : Location → Prop) (expected : Exit) : QueueValid allowed expected {} := by
  constructor <;> simp

theorem QueueValid.enqueue {allowed : Location → Prop} {expected : Exit} {state : Durable}
    (valid : QueueValid allowed expected state) {location : Location} (known : allowed location) :
    QueueValid allowed expected (enqueueOp location state) := by
  refine ⟨?_, valid.2⟩
  intro message member
  simp only [enqueueOp, LeaseQueueModel.enqueue, Array.mem_push] at member
  rcases member with previous | same
  · exact valid.1 _ previous
  · cases same; exact known

theorem QueueValid.ack {allowed : Location → Prop} {expected : Exit} {state : Durable}
    (valid : QueueValid allowed expected state) (receipt : Receipt) : QueueValid allowed expected (ackOp receipt state) := by
  refine ⟨?_, valid.2⟩
  intro message member
  change some message ∈ (LeaseQueueModel.acknowledge receipt state.transport).2.messages at member
  unfold LeaseQueueModel.acknowledge at member
  cases selected : current receipt state.transport with
  | none => exact valid.1 _ (by simpa only [selected] using member)
  | some old =>
    simp only [selected] at member
    have previous : some message ∈ state.transport.messages := by
      rcases Array.mem_or_eq_of_mem_setIfInBounds member with previous | same
      · exact previous
      · cases same
    exact valid.1 _ previous

theorem QueueValid.done {allowed : Location → Prop} {expected : Exit} {state : Durable}
    (valid : QueueValid allowed expected state) {outcome : Exit} (same : outcome = expected) :
    QueueValid allowed expected (doneOp outcome state) := by
  refine ⟨valid.1, ?_⟩
  intro returned recorded
  cases recorded
  exact same

/-- Leasing changes visibility and receipts, never the program location. -/
theorem QueueValid.dequeue {allowed : Location → Prop} {expected : Exit} {state : Durable}
    (valid : QueueValid allowed expected state) (duration : Nat) :
    QueueValid allowed expected { state with transport := (LeaseQueueModel.dequeue duration state.transport).2 } := by
  unfold LeaseQueueModel.dequeue
  split
  · exact valid
  · split
    · rename_i index _ message stored
      refine ⟨?_, valid.2⟩
      intro selected member
      rcases Array.mem_or_eq_of_mem_setIfInBounds member with previous | same
      · exact valid.1 _ previous
      · cases same
        exact valid.1 message (Array.mem_of_getElem? stored)
    · exact valid

theorem QueueValid.advance {allowed : Location → Prop} {expected : Exit} {state : Durable}
    (valid : QueueValid allowed expected state) (elapsed : Nat) :
    QueueValid allowed expected { state with transport := LeaseQueueModel.advance elapsed state.transport } := valid

/-- An ordinary poll returns either an idle worker, the intended durable result,
or an allowed location with the receipt of a message still in the transport. -/
def PollValid (allowed : Location → Prop) (expected : Exit) (returned : Work × Worker) (state : Durable) : Prop :=
  QueueValid allowed expected state ∧
    match returned.1 with
    | .idle => returned.2.delivery = none
    | .completed outcome => outcome = expected ∧ state.completed = some outcome ∧ returned.2.delivery = none
    | .item location => allowed location ∧ ∃ receipt message,
        returned.2.delivery = some (location, receipt) ∧
        current receipt state.transport = some message ∧ message.value = location

theorem QueueValid.next_spec (allowed : Location → Prop) (expected : Exit) (worker : Worker) :
    Triple (QueueValid allowed expected) (queue.next worker)
      (PollValid allowed expected) (QueueValid allowed expected) := by
  rw [next_eq]
  have read : Triple (QueueValid allowed expected)
      (atomic fun state : Durable => (state.completed, state))
      (fun completed state => completed = state.completed ∧ QueueValid allowed expected state)
      (QueueValid allowed expected) :=
    Triple.atomic _ (fun _ valid => ⟨rfl, valid⟩) (fun _ h => h) (fun _ h => h)
  apply read.bind
  intro completed
  cases completed with
  | some outcome =>
    apply (Triple.pure _ _).weaken (fun _ h => h) _ (fun _ h => h)
    intro returned state h
    obtain ⟨rfl, recorded, valid⟩ := h
    exact ⟨valid, valid.2 outcome recorded.symm, recorded.symm, rfl⟩
  | none =>
    have selected : Triple (QueueValid allowed expected)
        (atomic fun state : Durable =>
          let (delivery, next) := LeaseQueueModel.dequeue 1 state.transport
          (delivery, { state with transport := next }))
        (fun delivery state => QueueValid allowed expected state ∧ ∀ selected, delivery = some selected →
          ∃ message, current selected.receipt state.transport = some message ∧ message.value = selected.value)
        (QueueValid allowed expected) := by
      apply Triple.atomic
      · intro state valid
        refine ⟨valid.dequeue 1, ?_⟩
        intro delivery returned
        obtain ⟨message, current, value, _⟩ := LeaseQueue.dequeue_retains
          (show LeaseQueueModel.dequeue 1 state.transport =
            (some delivery, (LeaseQueueModel.dequeue 1 state.transport).2) from
            (Prod.eta _).symm.trans (congrArg (fun d => (d, (LeaseQueueModel.dequeue 1 state.transport).2)) returned))
        exact ⟨message, current, value⟩
      · exact fun _ h => h
      · exact fun _ h => h.dequeue 1
    apply (selected.weaken (fun _ h => h.2) (fun _ _ h => h) (fun _ h => h)).bind
    intro delivery
    cases delivery <;>
      apply (Triple.pure _ _).weaken (fun _ h => h) _ (fun _ h => h) <;>
      intro returned state h <;>
      obtain ⟨rfl, valid, retained⟩ := h
    · exact ⟨valid, rfl⟩
    · rename_i delivery
      obtain ⟨message, held, value⟩ := retained delivery rfl
      have allowedValue := valid.1 message (Array.mem_of_getElem? (LeaseQueue.current_iff.mp held).1)
      exact ⟨valid, value ▸ allowedValue, delivery.receipt, message, rfl, held, value⟩

theorem QueueValid.initial {allowed : Location → Prop} (expected : Exit) (root : allowed Location.root) :
    QueueValid allowed expected (enqueueOp Location.root {}) :=
  (QueueValid.empty allowed expected).enqueue root

private theorem QueueValid.operation {allowed : Location → Prop} {expected : Exit} {response : StepResult}
    (emits : match response with
      | .done outcome => outcome = expected
      | .runnable locations => ∀ location ∈ locations, allowed location) (receipt : Receipt) (operation : Durable → Durable)
    (member : operation ∈ operations receipt response) :
    ∀ state, QueueValid allowed expected state → QueueValid allowed expected (operation state) := by
  cases response with
  | done outcome =>
    simp only [operations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact fun _ valid => valid.done emits
    · exact fun _ valid => valid.ack receipt
  | runnable locations =>
    simp only [operations, List.mem_append, List.mem_map, List.mem_singleton] at member
    rcases member with ⟨location, member, rfl⟩ | rfl
    · exact fun _ valid => valid.enqueue (emits location (by simpa using member))
    · exact fun _ valid => valid.ack receipt

private theorem execute_spec (invariant : Durable → Prop) (ops : List (Durable → Durable))
    (preserves : ∀ operation ∈ ops, ∀ state, invariant state → invariant (operation state)) :
    Triple invariant (execute ops) (fun _ state => invariant state) invariant := by
  induction ops with
  | nil =>
    exact (Triple.pure invariant ()).weaken (fun _ h => h) (fun _ _ h => h.2) (fun _ h => h)
  | cons operation rest ih =>
    have first : Triple invariant (atomic fun state => ((), operation state))
        (fun _ state => invariant state) invariant :=
      Triple.atomic _ (preserves operation (by simp)) (fun _ h => h) (preserves operation (by simp))
    exact first.bind (fun _ => ih (fun op member => preserves op (by simp [member])))

/-- The actual publication call preserves validity on both return and crash.
Normal return clears the receipt; interruption consumes a fault entry, so this
specification composes with worker steps and the outer restart runner. -/
theorem QueueValid.complete_spec {allowed : Location → Prop} {expected : Exit}
    (location : Location) (receipt : Receipt) (response : StepResult)
    (emits : match response with
      | .done outcome => outcome = expected
      | .runnable locations => ∀ location ∈ locations, allowed location) :
    Triple (QueueValid allowed expected) (queue.complete location response ⟨(), some (location, receipt)⟩)
      (fun returned state => returned = ((), (⟨(), none⟩ : Worker)) ∧ QueueValid allowed expected state)
      (QueueValid allowed expected) := by
  rw [complete_eq]
  have sequence := execute_spec (QueueValid allowed expected) (operations receipt response)
    (fun op member => QueueValid.operation emits receipt op member)
  exact (sequence.map (fun _ : Unit => ((), (⟨(), none⟩ : Worker)))).weaken
    (fun _ h => h) (fun _ _ ⟨_, same, valid⟩ => ⟨same, valid⟩) (fun _ h => h)

/-- Every visible or leased payload has durable reconstruction prerequisites. -/
abbrev ActivatedQueue (tree : ExecutionTree) (journal : Journal) :=
  QueueValid (tree.Activated journal) tree.exit

theorem ActivatedQueue.grow {tree before after state}
    (valid : ActivatedQueue tree before state) (growth : JournalAdapter.Extends before after) :
    ActivatedQueue tree after state :=
  ⟨fun message member => (valid.1 message member).grow growth, valid.2⟩

theorem ActivatedQueue.initial (tree : ExecutionTree) (journal : Journal) :
    ActivatedQueue tree journal (enqueueOp Location.root {}) :=
  QueueValid.initial tree.exit (ExecutionTree.Activated.root tree journal)

/-- Polling derives the selected worker's routing preconditions from the queue
invariant and durable records. No successful step or ready path is assumed. -/
theorem next_delivery_ready {m : Type → Type} {program : Cloud m Json} {tree journal}
    (expansion : Expansion program tree) (bounded : JournalAdapter.Extends journal (tree.journal Location.root))
    (causal : ExecutionTree.Causal tree Location.root journal) (worker : Worker) :
    Triple (ActivatedQueue tree journal) (queue.next worker)
      (fun returned state => PollValid (tree.Activated journal) tree.exit returned state ∧
        ∀ location, returned.1 = .item location →
          ∃ node, ∃ route : TreeRoute tree Location.root location node,
            route.Activated journal ∧
              ((route.Ready journal ∧ OpenParent journal location) ∨ Obsolete journal location))
      (ActivatedQueue tree journal) := by
  apply (QueueValid.next_spec (tree.Activated journal) tree.exit worker).weaken (fun _ h => h) _ (fun _ h => h)
  intro returned state valid
  refine ⟨valid, ?_⟩
  intro location selected
  have delivered := valid.2
  rw [selected] at delivered
  obtain ⟨node, route, active⟩ := delivered.1
  exact ⟨node, route, active, route.delivery_ready expansion bounded causal active⟩

end LeanCloud.Proofs.LeasePublication
