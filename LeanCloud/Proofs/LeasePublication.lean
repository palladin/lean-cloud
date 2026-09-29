import LeanCloud.LeaseQueue
import LeanCloud.Proofs.LeaseQueue
import LeanCloud.Proofs.Crash
import Init.Data.Array.Monadic

/-! Publication-before-acknowledgement for the actual lease adapter. The backend
uses the ideal queue and separately atomic operations. Attempts are serialized;
neither fairness nor full replay recovery is assumed or proved here. -/

namespace LeanCloud.Proofs.LeasePublication
open CrashModel CrashRecovery LeaseQueueModel

structure Durable where
  transport : LeaseQueueModel.State Location := {}
  completed : Option Exit := none

abbrev M := CrashModel.M Durable
abbrev Worker := LeanCloud.LeaseQueue.Worker Unit Receipt

/-- A finite sequence of individually atomic transitions, used only to describe
the adapter's already existing sequence of backend calls. -/
def execute {δ : Type} : List (δ → δ) → CrashModel.M δ Unit
  | [] => pure ()
  | operation :: rest => do
    let _ ← atomic fun state => ((), operation state)
    execute rest

def applyOps {δ : Type} (operations : List (δ → δ)) (state : δ) : δ :=
  operations.foldl (fun state operation => operation state) state

/-- A crash leaves exactly a committed prefix, possibly including the operation
whose reply was lost. A normal return commits the entire sequence. -/
theorem execute_prefix {δ : Type} (operations : List (δ → δ)) (start : CrashModel.State δ) :
    let (result, final) := (execute operations).run start
    ∃ count, count ≤ operations.length ∧
      final.durable = applyOps (operations.take count) start.durable ∧
      (result = .ok () → count = operations.length) := by
  induction operations generalizing start with
  | nil => exact ⟨0, Nat.le_refl _, rfl, fun _ => rfl⟩
  | cons operation rest ih =>
    have observation := atomic_observation (fun state => ((), operation state)) start
    unfold execute
    rw [run_bind]
    generalize called : (atomic fun state => ((), operation state)).run start = first at *
    rcases first with ⟨result, middle⟩
    cases result with
    | error crash =>
      rcases observation.2.2 with old | committed
      · exact ⟨0, by simp, old, by simp⟩
      · exact ⟨1, by simp, committed, by simp⟩
    | ok value =>
      have tail := ih middle
      change ∃ count, count ≤ (operation :: rest).length ∧
        ((execute rest).run middle).2.durable = applyOps ((operation :: rest).take count) start.durable ∧
        (((execute rest).run middle).1 = .ok () → count = (operation :: rest).length)
      obtain ⟨count, bound, committed, complete⟩ := tail
      refine ⟨count + 1, by simpa using Nat.succ_le_succ bound, ?_, ?_⟩
      · simpa [applyOps, observation.2.2, ExceptT.run] using committed
      · intro returned
        simp [complete returned]

def enqueueOp (location : Location) (state : Durable) : Durable :=
  { state with transport := (LeaseQueueModel.enqueue location state.transport).2 }

def ackOp (receipt : Receipt) (state : Durable) : Durable :=
  { state with transport := (LeaseQueueModel.acknowledge receipt state.transport).2 }

def doneOp (outcome : Exit) (state : Durable) : Durable :=
  { state with completed := some outcome }

def transport : LeanCloud.LeaseQueue Unit M Receipt where
  enqueue location _ := atomic fun state => (((), ()), enqueueOp location state)
  dequeue _ := atomic fun state =>
    let (delivery, next) := LeaseQueueModel.dequeue 1 state.transport
    ((delivery.map (fun d => (d.value, d.receipt)), ()), { state with transport := next })
  acknowledge receipt _ := atomic fun state =>
    let (accepted, next) := LeaseQueueModel.acknowledge receipt state.transport
    ((accepted, ()), { state with transport := next })

def readCompleted : StateT Unit M (Option Exit) := fun _ =>
  atomic fun state => ((state.completed, ()), state)

def writeCompleted (outcome : Exit) : StateT Unit M Unit := fun _ =>
  atomic fun state => (((), ()), doneOp outcome state)

def queue : WorkQueue Worker M := transport.toWorkQueue readCompleted writeCompleted

def operations (receipt : Receipt) : StepResult → List (Durable → Durable)
  | .runnable locations => locations.toList.map enqueueOp ++ [ackOp receipt]
  | .done outcome => [doneOp outcome, ackOp receipt]

private theorem execute_append {δ : Type} (first last : List (δ → δ)) :
    execute (first ++ last) = (execute first >>= fun _ => execute last) := by
  induction first with
  | nil => simp [execute]
  | cons operation rest ih => simp [execute, ih, bind_assoc]

private theorem lift_atomic (operation : Durable → α × Durable) (worker : Worker) :
    LeanCloud.LeaseQueue.liftBackend (fun _ : Unit =>
      atomic fun state => let (value, next) := operation state; ((value, ()), next)) worker =
      (fun value => (value, worker)) <$> atomic operation := by
  rcases worker with ⟨handle, delivery⟩
  cases handle
  unfold LeanCloud.LeaseQueue.liftBackend
  rw [atomic_map operation (fun value => (value, ()))]
  simp only [bind_map_left]
  rfl

private theorem enqueue_lift (location : Location) (worker : Worker) :
    LeanCloud.LeaseQueue.liftBackend (transport.enqueue location) worker =
      (fun value : Unit => (value, worker)) <$> atomic (fun state => ((), enqueueOp location state)) := by
  simpa only [transport] using lift_atomic (fun state => ((), enqueueOp location state)) worker

private theorem done_lift (outcome : Exit) (worker : Worker) :
    LeanCloud.LeaseQueue.liftBackend (writeCompleted outcome) worker =
      (fun value : Unit => (value, worker)) <$> atomic (fun state => ((), doneOp outcome state)) := by
  unfold writeCompleted
  exact lift_atomic (fun state => ((), doneOp outcome state)) worker

private theorem ack_lift (receipt : Receipt) (worker : Worker) :
    LeanCloud.LeaseQueue.liftBackend (transport.acknowledge receipt) worker =
      (fun value : Bool => (value, worker)) <$> atomic (fun state =>
        ((LeaseQueueModel.acknowledge receipt state.transport).1, ackOp receipt state)) := by
  simpa only [transport, ackOp] using lift_atomic (fun state =>
    ((LeaseQueueModel.acknowledge receipt state.transport).1, ackOp receipt state)) worker

private theorem enqueue_loop (locations : List Location) (worker : Worker) :
    (forIn locations PUnit.unit fun location _ => do
      LeanCloud.LeaseQueue.liftBackend (transport.enqueue location)
      pure (ForInStep.yield PUnit.unit)) worker =
      (fun _ : Unit => (PUnit.unit, worker)) <$> execute (locations.map enqueueOp) := by
  induction locations with
  | nil => rfl
  | cons location rest ih =>
    rw [List.forIn_cons]
    simp only [bind_assoc, pure_bind]
    change (do
      let _ ← LeanCloud.LeaseQueue.liftBackend (transport.enqueue location)
      forIn rest PUnit.unit (fun location _ => do
        LeanCloud.LeaseQueue.liftBackend (transport.enqueue location)
        pure (ForInStep.yield PUnit.unit))).run worker = _
    rw [StateT.run_bind]
    simp only [StateT.run, enqueue_lift, List.map_cons, execute,
      bind_map_left, map_bind]
    congr 1
    funext value
    cases value
    exact ih

private theorem acknowledge_clear (receipt : Receipt) (worker : Worker) :
    (do
      let _ ← LeanCloud.LeaseQueue.liftBackend (transport.acknowledge receipt)
      modify fun worker : Worker => { worker with delivery := none }) worker =
      (fun _ : Unit => ((), { worker with delivery := none })) <$> execute [ackOp receipt] := by
  change (do
    let _ ← LeanCloud.LeaseQueue.liftBackend (transport.acknowledge receipt)
    modify fun worker : Worker => { worker with delivery := none }).run worker = _
  rw [StateT.run_bind]
  simp only [StateT.run, ack_lift, bind_map_left]
  have erase := atomic_map (fun state : Durable =>
    ((LeaseQueueModel.acknowledge receipt state.transport).1, ackOp receipt state))
    (fun _ : Bool => ())
  have single : execute [ackOp receipt] = atomic (fun state => ((), ackOp receipt state)) := by
    simp only [execute]
    rw [show (fun _ : Unit => (pure () : M Unit)) = pure from by funext u; cases u; rfl]
    exact bind_pure _
  rw [single, erase, Functor.map_map]
  congr 1

/-- For the current delivery, the actual adapter performs precisely the
publication operations followed by acknowledgement, each separately atomic. -/
theorem complete_eq (location : Location) (receipt : Receipt) (response : StepResult) :
    queue.complete location response ⟨(), some (location, receipt)⟩ =
      (fun _ : Unit => ((), (⟨(), none⟩ : Worker))) <$> execute (operations receipt response) := by
  change (queue.complete location response).run ⟨(), some (location, receipt)⟩ = _
  simp only [queue, LeanCloud.LeaseQueue.toWorkQueue, StateT.run_bind, StateT.run_get,
    pure_bind, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  cases response with
  | done outcome =>
    change (do
      LeanCloud.LeaseQueue.liftBackend (writeCompleted outcome)
      let _ ← LeanCloud.LeaseQueue.liftBackend (transport.acknowledge receipt)
      modify fun worker : Worker => { worker with delivery := none }).run ⟨(), some (location, receipt)⟩ = _
    rw [StateT.run_bind]
    simp only [done_lift, acknowledge_clear, StateT.run,
      operations, execute, bind_map_left, map_bind]
  | runnable locations =>
    change (do
      let _ ← forIn locations PUnit.unit fun location _ => do
        LeanCloud.LeaseQueue.liftBackend (transport.enqueue location)
        pure (ForInStep.yield PUnit.unit)
      let _ ← LeanCloud.LeaseQueue.liftBackend (transport.acknowledge receipt)
      modify fun worker : Worker => { worker with delivery := none }).run ⟨(), some (location, receipt)⟩ = _
    rw [StateT.run_bind, ← Array.forIn_toList]
    simp only [enqueue_loop, acknowledge_clear, StateT.run, operations, execute_append,
      bind_map_left, map_bind]

/-- The adapter can stop at any physical operation, but cannot skip ahead to
acknowledgement without committing the preceding publications. -/
theorem complete_prefix (location : Location) (receipt : Receipt) (response : StepResult)
    (start : CrashModel.State Durable) :
    let final := ((queue.complete location response ⟨(), some (location, receipt)⟩).run start).2
    ∃ count, count ≤ (operations receipt response).length ∧
      final.durable = applyOps ((operations receipt response).take count) start.durable := by
  rw [complete_eq, run_map]
  obtain ⟨count, bound, committed, _⟩ := execute_prefix (operations receipt response) start
  exact ⟨count, bound, committed⟩

/-- Exact queue shape after publishing a list. New messages occupy distinct
slots beyond every slot that existed before publication. -/
def enqueued (locations : List Location) (state : Durable) : Durable :=
  { state with transport.messages := state.transport.messages ++
      (locations.map fun location => some ({ value := location, visibleAt := state.transport.now } : Message Location)).toArray }

theorem apply_enqueue (locations : List Location) (state : Durable) :
    applyOps (locations.map enqueueOp) state = enqueued locations state := by
  induction locations generalizing state with
  | nil => simp [applyOps, enqueued]
  | cons location rest ih =>
    change applyOps (rest.map enqueueOp) (enqueueOp location state) = _
    rw [ih]
    simp [enqueued, enqueueOp, LeaseQueueModel.enqueue, Array.push_eq_append,
      Array.append_assoc, -Array.append_singleton]

/-- Every interrupted runnable completion is either an unacknowledged enqueue
prefix or the full publication followed by acknowledgement. -/
theorem runnable_cases (location : Location) (receipt : Receipt) (locations : Array Location)
    (start : CrashModel.State Durable) :
    let final := ((queue.complete location (.runnable locations) ⟨(), some (location, receipt)⟩).run start).2.durable
    (∃ count, count ≤ locations.size ∧ final = enqueued (locations.toList.take count) start.durable) ∨
      final = ackOp receipt (enqueued locations.toList start.durable) := by
  obtain ⟨count, bound, committed⟩ := complete_prefix location receipt (.runnable locations) start
  simp only [operations, List.length_append, List.length_map, Array.length_toList, List.length_singleton] at bound
  by_cases beforeAck : count ≤ locations.size
  · left
    refine ⟨count, beforeAck, ?_⟩
    rw [committed]
    have take : count ≤ (locations.toList.map enqueueOp).length := by
      simpa only [List.length_map, Array.length_toList] using beforeAck
    simp only [operations, List.take_append_of_le_length take, ← List.map_take, apply_enqueue]
  · right
    have all : count = locations.size + 1 := by omega
    rw [committed]
    have length : count = (operations receipt (.runnable locations)).length := by simpa [operations] using all
    rw [length, List.take_length]
    simp only [operations, applyOps, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change ackOp receipt (applyOps (locations.toList.map enqueueOp) start.durable) = _
    rw [apply_enqueue]

/-- Each successor has its own new slot, including equal successor locations.
This is stronger than merely finding a matching payload somewhere in the queue. -/
def Fresh (locations : Array Location) (start final : Durable) : Prop :=
  ∀ i, i < locations.size → ∃ message,
    final.transport.messages[start.transport.messages.size + i]? = some (some message) ∧
      message.value = locations[i]!

theorem enqueued_old (locations : List Location) (state : Durable) (index : Nat)
    (inside : index < state.transport.messages.size) :
    (enqueued locations state).transport.messages[index]? = state.transport.messages[index]? := by
  simp [enqueued, Array.getElem?_append, inside]

theorem enqueued_fresh (locations : Array Location) (state : Durable) :
    Fresh locations state (enqueued locations.toList state) := by
  intro i inside
  refine ⟨⟨locations[i], 0, state.transport.now⟩, ?_, ?_⟩
  · simp [enqueued, inside]
  · simp [getElem!_pos, inside]

theorem ack_fresh (receipt : Receipt) (locations : Array Location) (start published : Durable)
    (inside : receipt.message < start.transport.messages.size) (fresh : Fresh locations start published) :
    Fresh locations start (ackOp receipt published) := by
  intro i bound
  obtain ⟨message, stored, value⟩ := fresh i bound
  refine ⟨message, ?_, value⟩
  change (LeaseQueueModel.acknowledge receipt published.transport).2.messages[_]? = _
  rw [LeaseQueue.acknowledge_preserves_other receipt published.transport _ (by omega)]
  exact stored

/-- No lost runnable work: the incoming delivery's slot survives, or every
successor has been durably placed in its own slot and survives acknowledgement.
The statement covers crashes before and after every primitive, and normal return. -/
theorem complete_no_loss (location : Location) (receipt : Receipt) (locations : Array Location)
    (start : CrashModel.State Durable) (message : Message Location)
    (valid : current receipt start.durable.transport = some message) :
    let final := ((queue.complete location (.runnable locations) ⟨(), some (location, receipt)⟩).run start).2.durable
    final.transport.messages[receipt.message]? = some (some message) ∨ Fresh locations start.durable final := by
  have stored := (LeaseQueue.current_iff.mp valid).1
  have inside := (Array.getElem?_eq_some_iff.mp stored).choose
  rcases runnable_cases location receipt locations start with ⟨count, _, published⟩ | acknowledged
  · left
    rw [published, enqueued_old _ _ _ inside]
    exact stored
  · right
    rw [acknowledged]
    exact ack_fresh receipt locations _ _ inside (enqueued_fresh locations start.durable)

/-- Completion follows the same rule: either the original delivery is retained
or the final result is already durable. -/
theorem done_no_loss (location : Location) (receipt : Receipt) (outcome : Exit)
    (start : CrashModel.State Durable) (message : Message Location)
    (valid : current receipt start.durable.transport = some message) :
    let final := ((queue.complete location (.done outcome) ⟨(), some (location, receipt)⟩).run start).2.durable
    final.transport.messages[receipt.message]? = some (some message) ∨ final.completed = some outcome := by
  obtain ⟨count, bound, committed⟩ := complete_prefix location receipt (.done outcome) start
  have stored := (LeaseQueue.current_iff.mp valid).1
  simp only [operations, List.length_cons, List.length_nil] at bound
  have cases : count = 0 ∨ count = 1 ∨ count = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · left
    simpa [committed, operations, applyOps] using stored
  · right
    simp [committed, operations, applyOps, doneOp]
  · right
    simp [committed, operations, applyOps, doneOp, ackOp]

/-- Normal return commits every publication and attempts acknowledgement, then
clears the worker's receipt. An invalid acknowledgement may still return normally. -/
theorem complete_returned (location : Location) (receipt : Receipt) (response : StepResult)
    (start final : CrashModel.State Durable) (worker : Worker)
    (returned : (queue.complete location response ⟨(), some (location, receipt)⟩).run start =
      (.ok ((), worker), final)) :
    final.durable = applyOps (operations receipt response) start.durable ∧ worker.delivery = none := by
  have observed := execute_prefix (operations receipt response) start
  rw [complete_eq, run_map] at returned
  generalize execution : (execute (operations receipt response)).run start = run at *
  rcases run with ⟨result, committed⟩
  cases result with
  | error crash => cases returned
  | ok value =>
    cases value
    simp only [Except.map] at returned
    rcases returned with ⟨same, rfl⟩
    obtain ⟨count, _, durable, full⟩ := observed
    rw [full rfl, List.take_length] at durable
    exact ⟨durable, rfl⟩

/-- A stale worker cannot delete the newer delivery occupying its old message
slot. Enqueues preserve the slot and the ideal queue rejects the stale receipt. -/
theorem stale_completion_preserves (location : Location) (receipt : Receipt) (locations : Array Location)
    (start : CrashModel.State Durable) (message : Message Location)
    (stored : start.durable.transport.messages[receipt.message]? = some (some message))
    (stale : current receipt start.durable.transport = none) :
    let final := ((queue.complete location (.runnable locations) ⟨(), some (location, receipt)⟩).run start).2.durable
    final.transport.messages[receipt.message]? = some (some message) := by
  dsimp only
  have inside := (Array.getElem?_eq_some_iff.mp stored).choose
  rcases runnable_cases location receipt locations start with ⟨count, _, published⟩ | acknowledged
  · rw [published, enqueued_old _ _ _ inside]
    exact stored
  · rw [acknowledged]
    have stillStale : current receipt (enqueued locations.toList start.durable).transport = none := by
      unfold current
      rw [enqueued_old _ _ _ inside]
      exact stale
    simp only [ackOp, LeaseQueue.invalid_acknowledge receipt _ stillStale]
    rw [enqueued_old _ _ _ inside]
    exact stored

/-- A call without an active delivery cannot publish or acknowledge anything. -/
theorem complete_without_delivery (location : Location) (response : StepResult) :
    queue.complete location response ⟨(), none⟩ = pure ((), (⟨(), none⟩ : Worker)) := by
  change (queue.complete location response).run ⟨(), none⟩ = _
  simp [queue, LeanCloud.LeaseQueue.toWorkQueue, StateT.run_bind, StateT.run_get, StateT.run_pure]

/-- Completing a different location preserves the active receipt and performs
no backend calls. -/
theorem complete_foreign (location delivered : Location) (receipt : Receipt) (response : StepResult)
    (different : delivered ≠ location) :
    queue.complete location response ⟨(), some (delivered, receipt)⟩ =
      pure ((), (⟨(), some (delivered, receipt)⟩ : Worker)) := by
  change (queue.complete location response).run ⟨(), some (delivered, receipt)⟩ = _
  simp [queue, LeanCloud.LeaseQueue.toWorkQueue, StateT.run_bind, StateT.run_get,
    StateT.run_pure, different]

private theorem read_lift (worker : Worker) :
    LeanCloud.LeaseQueue.liftBackend readCompleted worker =
      (fun value => (value, worker)) <$> atomic (fun state => (state.completed, state)) := by
  unfold readCompleted
  exact lift_atomic (fun state => (state.completed, state)) worker

/-- The two physical operations performed by `next`. Dequeue is skipped when
the durable result exists; the worker's old delivery is always discarded. -/
theorem next_eq (worker : Worker) :
    queue.next worker = (do
      let completed ← atomic fun state : Durable => (state.completed, state)
      match completed with
      | some outcome => pure (.completed outcome, ⟨(), none⟩)
      | none =>
        let delivery ← atomic fun state : Durable =>
          let (delivery, next) := LeaseQueueModel.dequeue 1 state.transport
          (delivery, { state with transport := next })
        match delivery with
        | none => pure (.idle, ⟨(), none⟩)
        | some delivery => pure (.item delivery.value, ⟨(), some (delivery.value, delivery.receipt)⟩)) := by
  rcases worker with ⟨handle, delivery⟩
  cases handle
  change ((queue.next).run ⟨(), delivery⟩) = _
  simp only [queue, LeanCloud.LeaseQueue.toWorkQueue, StateT.run_bind, StateT.run_modify, pure_bind]
  simp only [StateT.run, read_lift, bind_map_left]
  congr 1
  funext completed
  cases completed with
  | some outcome => rfl
  | none =>
    have lifted := lift_atomic (fun state : Durable =>
      let (delivery, next) := LeaseQueueModel.dequeue 1 state.transport
      (delivery.map (fun d => (d.value, d.receipt)), { state with transport := next })) (⟨(), none⟩ : Worker)
    simp only [transport]
    change StateT.run _ _ = _
    rw [StateT.run_bind]
    simp only [StateT.run]
    rw [lifted]
    simp only [bind_map_left]
    rw [atomic_map (fun state : Durable =>
      let (delivery, next) := LeaseQueueModel.dequeue 1 state.transport
      (delivery, { state with transport := next })) (fun delivery => delivery.map (fun d => (d.value, d.receipt)))]
    simp only [bind_map_left]
    congr 1
    funext selected
    cases selected <;> rfl

/-- When completion is durable, restarting `next` performs only its completion
read. It neither dequeues nor acknowledges leftover transport messages, even if
the worker crashes on either side of that atomic read. -/
theorem next_completed (worker : Worker) (outcome : Exit) (start : CrashModel.State Durable)
    (cached : start.durable.completed = some outcome) :
    (queue.next worker).run start =
      ((fun _ : Option Exit => (Work.completed outcome, (⟨(), none⟩ : Worker))) <$>
        atomic (fun state : Durable => (state.completed, state))).run start := by
  rcases worker with ⟨handle, delivery⟩
  cases handle
  change ((queue.next).run ⟨(), delivery⟩).run start = _
  simp only [queue, LeanCloud.LeaseQueue.toWorkQueue, StateT.run_bind, StateT.run_modify, pure_bind]
  simp only [StateT.run, read_lift, bind_map_left]
  rw [run_bind, run_map]
  have observation := atomic_observation (fun state : Durable => (state.completed, state)) start
  generalize called : (atomic fun state : Durable => (state.completed, state)).run start = read at *
  rcases read with ⟨result, committed⟩
  cases result with
  | error crash => rfl
  | ok value =>
    have valueKnown := observation.2.1.trans cached
    subst value
    rfl

end LeanCloud.Proofs.LeasePublication
