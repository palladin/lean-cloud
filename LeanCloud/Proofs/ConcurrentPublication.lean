import LeanCloud.Proofs.SimulationComposition
import LeanCloud.Proofs.LeaseQueue
import LeanCloud.SimulationBackend
import Init.Data.Array.Monadic

/-! Concurrent publication requests to the actual lease adapter. Incoming
receipts refer to a fixed initial set of slots; published successors occupy new
slots. This isolates handoff from subsequent processing of those successors. -/

namespace LeanCloud.Proofs.ConcurrentPublication
open Lean LeanEff Simulation SimulationBackend LeaseQueueModel

structure Request where
  location : Location
  receipt : Receipt
  response : StepResult

/-- A message is retained even while its lease makes it temporarily invisible. -/
def Retained (location : Location) (slot : Nat) (state : Durable) : Prop :=
  ∃ message, state.transport.messages[slot]? = some (some message) ∧ message.value = location

/-- Successors are in fresh queue slots, or the final result is durable. -/
def Published (cutoff : Nat) (response : StepResult) (state : Durable) : Prop :=
  match response with
  | .runnable locations => ∀ location ∈ locations, ∃ slot, cutoff ≤ slot ∧ Retained location slot state
  | .done outcome => state.completed = some outcome

def Covered (cutoff : Nat) (request : Request) (state : Durable) : Prop :=
  Retained request.location request.receipt.message state ∨ Published cutoff request.response state

/-- Retained work becomes eligible again after enough time passes. This is
availability, not a fairness claim that a particular dequeue selects it. -/
theorem Retained.available {location slot state} (retained : Retained location slot state) :
    ∃ elapsed message,
      (advance elapsed state).transport.messages[slot]? = some (some message) ∧
      message.value = location ∧ message.visible (advance elapsed state).transport.now = true := by
  obtain ⟨message, stored, value⟩ := retained
  exact ⟨message.visibleAt, message, stored, value, by
    simp [SimulationBackend.advance, LeaseQueueModel.advance, Message.visible]⟩

/-- During this handoff batch, fresh successors are not yet acknowledged.
Journal records and an existing final result also remain unchanged. -/
structure Grows (cutoff : Nat) (before after : Durable) : Prop where
  records : after.records = before.records
  size : before.transport.messages.size ≤ after.transport.messages.size
  fresh : ∀ slot, cutoff ≤ slot → ∀ message,
    before.transport.messages[slot]? = some (some message) →
      after.transport.messages[slot]? = some (some message)
  completed : ∀ outcome, before.completed = some outcome → after.completed = some outcome

theorem Grows.refl (cutoff : Nat) (state : Durable) : Grows cutoff state state :=
  ⟨rfl, Nat.le_refl _, fun _ _ _ stored => stored, fun _ stored => stored⟩

theorem Grows.trans {cutoff : Nat} {first middle last : Durable}
    (a : Grows cutoff first middle) (b : Grows cutoff middle last) : Grows cutoff first last :=
  ⟨b.records.trans a.records, Nat.le_trans a.size b.size,
    fun slot fresh message stored => b.fresh slot fresh message (a.fresh slot fresh message stored),
    fun outcome stored => b.completed outcome (a.completed outcome stored)⟩

theorem Published.grow {cutoff response before after}
    (published : Published cutoff response before) (growth : Grows cutoff before after) :
    Published cutoff response after := by
  cases response with
  | done outcome => exact growth.completed _ published
  | runnable locations =>
    intro location member
    obtain ⟨slot, fresh, message, stored, value⟩ := published location member
    exact ⟨slot, fresh, message, growth.fresh slot fresh message stored, value⟩

/-- Requests sharing an incoming slot must agree on the replacement work.
Final-result publications must agree on the workflow's outcome. -/
structure Batch (cutoff : Nat) (requests : Fin count → Request) (outcome : Exit) : Prop where
  receipts : ∀ worker, (requests worker).receipt.message < cutoff
  duplicates : ∀ left right, (requests left).receipt.message = (requests right).receipt.message →
    (requests left).response = (requests right).response
  final : ∀ worker result, (requests worker).response = .done result → result = outcome

def Valid (cutoff : Nat) (requests : Fin count → Request) (outcome : Exit) (state : Durable) : Prop :=
  cutoff ≤ state.transport.messages.size ∧
    (∀ result, state.completed = some result → result = outcome) ∧
    ∀ worker, Covered cutoff (requests worker) state

private def enqueued (location : Location) (state : Durable) : Durable :=
  { state with transport := (LeaseQueueModel.enqueue location state.transport).2 }

private def acknowledged (receipt : Receipt) (state : Durable) : Durable :=
  { state with transport := (LeaseQueueModel.acknowledge receipt state.transport).2 }

private def completed (outcome : Exit) (state : Durable) : Durable :=
  { state with completed := some outcome }

private theorem enqueue_grows (cutoff : Nat) (location : Location) (state : Durable) :
    Grows cutoff state (enqueued location state) := by
  refine ⟨rfl, by simp [enqueued, LeaseQueueModel.enqueue], ?_, fun _ stored => stored⟩
  intro slot fresh message stored
  have inside := (Array.getElem?_eq_some_iff.mp stored).choose
  simpa [enqueued, LeaseQueueModel.enqueue, Array.getElem?_push, inside, Nat.ne_of_lt inside] using stored

private theorem enqueue_valid {cutoff : Nat} {requests : Fin count → Request} {outcome : Exit} {state : Durable} (location : Location)
    (valid : Valid cutoff requests outcome state) : Valid cutoff requests outcome (enqueued location state) := by
  refine ⟨Nat.le_trans valid.1 (enqueue_grows cutoff location state).size, valid.2.1, ?_⟩
  intro worker
  rcases valid.2.2 worker with ⟨message, stored, value⟩ | published
  · left
    have inside := (Array.getElem?_eq_some_iff.mp stored).choose
    exact ⟨message, by simpa [enqueued, LeaseQueueModel.enqueue, Array.getElem?_push, inside, Nat.ne_of_lt inside] using stored, value⟩
  · exact .inr (published.grow (enqueue_grows cutoff location state))

private theorem enqueue_published {cutoff state} (location : Location)
    (size : cutoff ≤ state.transport.messages.size) :
    Published cutoff (.runnable #[location]) (enqueued location state) := by
  intro value member
  have same : value = location := by simpa using member
  subst value
  exact ⟨state.transport.messages.size, size, ⟨location, 0, state.transport.now⟩,
    by simp [enqueued, LeaseQueueModel.enqueue], rfl⟩

private theorem ack_grows {cutoff : Nat} (receipt : Receipt) (inside : receipt.message < cutoff) (state : Durable) :
    Grows cutoff state (acknowledged receipt state) := by
  refine ⟨rfl, ?_, ?_, fun _ stored => stored⟩
  · cases read : current receipt state.transport <;> simp [acknowledged, acknowledge, read]
  · intro slot fresh message stored
    change (acknowledge receipt state.transport).2.messages[slot]? = _
    rw [LeaseQueue.acknowledge_preserves_other receipt state.transport slot (by omega)]
    exact stored

private theorem ack_valid {cutoff : Nat} {requests : Fin count → Request} {outcome : Exit} {state : Durable}
    (batch : Batch cutoff requests outcome) (worker : Fin count)
    (valid : Valid cutoff requests outcome state)
    (published : Published cutoff (requests worker).response state) :
    Valid cutoff requests outcome (acknowledged (requests worker).receipt state) := by
  have growth := ack_grows (requests worker).receipt (batch.receipts worker) state
  refine ⟨Nat.le_trans valid.1 growth.size, valid.2.1, ?_⟩
  intro other
  rcases valid.2.2 other with ⟨message, stored, value⟩ | done
  · by_cases same : (requests worker).receipt.message = (requests other).receipt.message
    · right
      rw [← batch.duplicates worker other same]
      exact published.grow growth
    · left
      exact ⟨message, (LeaseQueue.acknowledge_preserves_other _ _ _ same).trans stored, value⟩
  · exact .inr (done.grow growth)

private theorem done_grows {cutoff : Nat} {requests : Fin count → Request} {outcome : Exit} {state : Durable}
    (valid : Valid cutoff requests outcome state) : Grows cutoff state (completed outcome state) := by
  refine ⟨rfl, Nat.le_refl _, fun _ _ _ stored => stored, ?_⟩
  intro result stored
  exact congrArg some (valid.2.1 result stored).symm

private theorem done_valid {cutoff : Nat} {requests : Fin count → Request} {outcome : Exit} {state : Durable}
    (valid : Valid cutoff requests outcome state) : Valid cutoff requests outcome (completed outcome state) := by
  refine ⟨valid.1, ?_, ?_⟩
  · intro result stored
    exact (Option.some.inj stored).symm
  · intro worker
    rcases valid.2.2 worker with retained | published
    · exact .inl retained
    · exact .inr (published.grow (done_grows valid))

private theorem enqueue_safe (cutoff : Nat) (requests : Fin count → Request) (outcome : Exit)
    (duration : Nat) (location : Location) (worker : SimulationBackend.Worker) (state : Durable) :
    Safe (Valid cutoff requests outcome) (Grows cutoff)
      (fun returned final => returned = ((), worker) ∧ Published cutoff (.runnable #[location]) final)
      (.ofProgram ((LeanCloud.LeaseQueue.liftBackend ((transport duration).enqueue location)).run worker)) state := by
  dsimp [LeanCloud.LeaseQueue.liftBackend, transport, StateT.run, SimM.atomic, EffF.send,
    bind, pure, EffF.bind, Simulation.Worker.ofProgram]
  apply Safe.waiting
  · intro current valid growth
    exact ⟨enqueue_valid location valid, enqueue_grows cutoff location current⟩
  · intro committed valid growth
    apply Safe.responding
    intro delivered deliveredValid later
    simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, Simulation.Worker.ofProgram]
    apply Safe.finished
    intro final finalValid last
    exact ⟨by cases worker with | mk backend delivery => cases backend; rfl,
      (enqueue_published location valid.1).grow (later.trans last)⟩

private theorem done_safe (cutoff : Nat) (requests : Fin count → Request) (outcome : Exit)
    (worker : SimulationBackend.Worker) (state : Durable) :
    Safe (Valid cutoff requests outcome) (Grows cutoff)
      (fun returned final => returned = ((), worker) ∧ final.completed = some outcome)
      (.ofProgram ((LeanCloud.LeaseQueue.liftBackend (writeCompleted outcome)).run worker)) state := by
  dsimp [LeanCloud.LeaseQueue.liftBackend, writeCompleted, StateT.run, SimM.atomic, EffF.send,
    bind, pure, EffF.bind, Simulation.Worker.ofProgram]
  apply Safe.waiting
  · intro current valid growth
    exact ⟨done_valid valid, done_grows valid⟩
  · intro committed valid growth
    apply Safe.responding
    intro delivered deliveredValid later
    simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, Simulation.Worker.ofProgram]
    apply Safe.finished
    intro final finalValid last
    exact ⟨by cases worker with | mk backend delivery => cases backend; rfl,
      (later.trans last).completed outcome rfl⟩

private theorem ack_safe {cutoff : Nat} {requests : Fin count → Request} {outcome : Exit}
    (batch : Batch cutoff requests outcome) (selected : Fin count) (duration : Nat)
    (worker : SimulationBackend.Worker) (state : Durable)
    (published : Published cutoff (requests selected).response state) :
    Safe (Valid cutoff requests outcome) (Grows cutoff)
      (fun returned final => returned.2 = worker ∧ Published cutoff (requests selected).response final)
      (.ofProgram ((LeanCloud.LeaseQueue.liftBackend
        ((transport duration).acknowledge (requests selected).receipt)).run worker)) state := by
  dsimp [LeanCloud.LeaseQueue.liftBackend, transport, StateT.run, SimM.atomic, EffF.send,
    bind, pure, EffF.bind, Simulation.Worker.ofProgram]
  apply Safe.waiting
  · intro current valid growth
    exact ⟨ack_valid batch selected valid (published.grow growth),
      ack_grows _ (batch.receipts selected) current⟩
  · intro committed valid growth
    apply Safe.responding
    intro delivered deliveredValid later
    simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, Simulation.Worker.ofProgram]
    apply Safe.finished
    intro final finalValid last
    exact ⟨by cases worker with | mk backend delivery => cases backend; rfl,
      published.grow ((growth.trans (ack_grows _ (batch.receipts selected) committed)).trans (later.trans last))⟩

private theorem state_bind {cutoff : Nat} {requests : Fin count → Request} {outcome : Exit}
    {action : StateT SimulationBackend.Worker M α} {next : α → StateT SimulationBackend.Worker M β}
    {first : (α × SimulationBackend.Worker) → Durable → Prop}
    {post : (β × SimulationBackend.Worker) → Durable → Prop} {worker : SimulationBackend.Worker} {state : Durable}
    (safe : Safe (Valid cutoff requests outcome) (Grows cutoff) first (.ofProgram (action.run worker)) state)
    (valid : Valid cutoff requests outcome state)
    (resume : ∀ returned current, Valid cutoff requests outcome current → Grows cutoff state current →
      first returned current → Safe (Valid cutoff requests outcome) (Grows cutoff) post
        (.ofProgram ((next returned.1).run returned.2)) current) :
    Safe (Valid cutoff requests outcome) (Grows cutoff) post (.ofProgram ((action >>= next).run worker)) state := by
  apply Safe.bind (Grows.refl cutoff) (fun a b => a.trans b)
    (safe.remember (fun a b => a.trans b) state (.refl _ _)) valid
  intro returned current kept h
  exact resume returned current kept h.1 h.2

private abbrev enqueueBody (duration : Nat) (location : Location) (_ : PUnit.{1}) :
    StateT SimulationBackend.Worker M (ForInStep PUnit.{1}) := do
  LeanCloud.LeaseQueue.liftBackend ((transport duration).enqueue location)
  pure (.yield PUnit.unit)

private theorem enqueue_list_safe (cutoff : Nat) (requests : Fin count → Request) (outcome : Exit)
    (duration : Nat) (locations : List Location) (worker : SimulationBackend.Worker) (state : Durable)
    (valid : Valid cutoff requests outcome state) :
    Safe (Valid cutoff requests outcome) (Grows cutoff)
      (fun returned final => returned = (PUnit.unit, worker) ∧ Published cutoff (.runnable locations.toArray) final)
      (.ofProgram ((forIn locations PUnit.unit (enqueueBody duration)).run worker)) state := by
  induction locations generalizing worker state with
  | nil =>
    apply Safe.finished
    intro final kept growth
    exact ⟨rfl, by simp [Published]⟩
  | cons location rest ih =>
    rw [List.forIn_cons]
    have first : Safe (Valid cutoff requests outcome) (Grows cutoff)
        (fun returned final => returned = (.yield PUnit.unit, worker) ∧ Published cutoff (.runnable #[location]) final)
        (.ofProgram ((enqueueBody duration location PUnit.unit).run worker)) state := by
      unfold enqueueBody
      apply state_bind (enqueue_safe cutoff requests outcome duration location worker state) valid
      intro returned current kept growth h
      obtain ⟨rfl, published⟩ := h
      exact .finished fun final finalValid later => ⟨rfl, published.grow later⟩
    apply state_bind first valid
    intro returned current kept growth h
    obtain ⟨rfl, head⟩ := h
    apply Safe.weaken ((ih worker current kept).remember (fun a b => a.trans b) current (.refl _ _))
    intro returned final finalValid h
    obtain ⟨later, rfl, tail⟩ := h
    refine ⟨rfl, ?_⟩
    intro item member
    have choices : item = location ∨ item ∈ rest := by simpa using member
    rcases choices with rfl | member
    · exact (head.grow later) item (by simp)
    · exact tail item (by simpa using member)

/-- Every primitive of the real completion adapter preserves batch coverage.
Returning also clears the local receipt and establishes replacement work. -/
theorem complete_safe {cutoff : Nat} {requests : Fin count → Request} {outcome : Exit}
    (batch : Batch cutoff requests outcome) (selected : Fin count) (duration : Nat)
    (state : Durable) (valid : Valid cutoff requests outcome state) :
    Safe (Valid cutoff requests outcome) (Grows cutoff)
      (fun returned final => returned = ((), (⟨(), none⟩ : SimulationBackend.Worker)) ∧
        Published cutoff (requests selected).response final)
      (.ofProgram (((queue duration).complete (requests selected).location (requests selected).response).run
        ⟨(), some ((requests selected).location, (requests selected).receipt)⟩)) state := by
  let worker : SimulationBackend.Worker := ⟨(), some ((requests selected).location, (requests selected).receipt)⟩
  have acknowledge (current : Durable) (kept : Valid cutoff requests outcome current)
      (published : Published cutoff (requests selected).response current) :
      Safe (Valid cutoff requests outcome) (Grows cutoff)
        (fun returned final => returned = ((), (⟨(), none⟩ : SimulationBackend.Worker)) ∧
          Published cutoff (requests selected).response final)
        (.ofProgram ((do
          let _ ← LeanCloud.LeaseQueue.liftBackend ((transport duration).acknowledge (requests selected).receipt)
          modify fun worker : SimulationBackend.Worker => { worker with delivery := none }).run worker)) current := by
    apply state_bind (ack_safe batch selected duration worker current published) kept
    intro returned delivered deliveredValid later h
    obtain ⟨same, published⟩ := h
    rcases returned with ⟨accepted, handle⟩
    dsimp only at same
    subst handle
    exact .finished fun final finalValid last => ⟨rfl, published.grow last⟩
  dsimp [queue, LeanCloud.LeaseQueue.toWorkQueue, StateT.run, StateT.bind, MonadState.get, getThe, MonadStateOf.get,
    StateT.get, bind, pure, EffF.bind]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  change Safe _ _ _ (.ofProgram ((do
    match (requests selected).response with
    | .runnable locations => for location in locations do
        LeanCloud.LeaseQueue.liftBackend ((transport duration).enqueue location)
    | .done result => LeanCloud.LeaseQueue.liftBackend (writeCompleted result)
    let _ ← LeanCloud.LeaseQueue.liftBackend ((transport duration).acknowledge (requests selected).receipt)
    modify fun worker : SimulationBackend.Worker => { worker with delivery := none }).run worker)) state
  cases response : (requests selected).response with
  | done result =>
    have same := batch.final selected result response
    subst result
    apply state_bind (done_safe cutoff requests outcome worker state) valid
    intro returned current kept growth h
    obtain ⟨rfl, published⟩ := h
    simpa only [response] using acknowledge current kept (by simpa only [response, Published] using published)
  | runnable locations =>
    dsimp only
    rw [← Array.forIn_toList]
    apply state_bind (enqueue_list_safe cutoff requests outcome duration locations.toList worker state valid) valid
    intro returned current kept growth h
    obtain ⟨rfl, published⟩ := h
    simpa only [response] using acknowledge current kept (by simpa only [response, Array.toArray_toList] using published)

/-- Concurrent handoff requests, including a crash or lost reply at any
primitive and reissuing the same request. This is request retry, not restoration
of a crashed worker's local receipt: a full worker must reacquire its delivery.
New successors are left for a later consumer stage. -/
theorem complete_concurrent (requests : Fin count → Request) (outcome : Exit) (duration : Nat)
    (initial : Durable)
    (retained : ∀ worker, Retained (requests worker).location (requests worker).receipt.message initial)
    (duplicates : ∀ left right, (requests left).receipt.message = (requests right).receipt.message →
      (requests left).response = (requests right).response)
    (agrees : ∀ worker result, (requests worker).response = .done result → result = outcome)
    (existing : ∀ result, initial.completed = some result → result = outcome)
    (events : List (Event count))
    (final : Simulation.State Durable (Unit × SimulationBackend.Worker) count)
    (executed :
      let start := fun worker =>
        ((queue duration).complete (requests worker).location (requests worker).response).run
          ⟨(), some ((requests worker).location, (requests worker).receipt)⟩
      Simulation.run start advance events (Simulation.State.initial initial start) = .ok final) :
    final.durable.records = initial.records ∧
      (∀ worker, Covered initial.transport.messages.size (requests worker) final.durable) ∧
      ∀ worker returned, (final.workers worker).outcome? = some returned →
        returned = ((), (⟨(), none⟩ : SimulationBackend.Worker)) ∧
          Published initial.transport.messages.size (requests worker).response final.durable := by
  let cutoff := initial.transport.messages.size
  let start := fun worker =>
    ((queue duration).complete (requests worker).location (requests worker).response).run
      ⟨(), some ((requests worker).location, (requests worker).receipt)⟩
  let post := fun worker (returned : Unit × SimulationBackend.Worker) final =>
    returned = ((), (⟨(), none⟩ : SimulationBackend.Worker)) ∧ Published cutoff (requests worker).response final
  have batch : Batch cutoff requests outcome := by
    refine ⟨?_, duplicates, agrees⟩
    intro worker
    obtain ⟨message, stored, value⟩ := retained worker
    exact (Array.getElem?_eq_some_iff.mp stored).choose
  have fresh worker state (valid : Valid cutoff requests outcome state) :
      Safe (Valid cutoff requests outcome) (Grows cutoff) (post worker) (.ofProgram (start worker)) state :=
    complete_safe batch worker duration state valid
  have clock elapsed state (valid : Valid cutoff requests outcome state) :
      Valid cutoff requests outcome (advance elapsed state) ∧ Grows cutoff state (advance elapsed state) :=
    ⟨valid, ⟨rfl, Nat.le_refl _, fun _ _ _ stored => stored, fun _ stored => stored⟩⟩
  have valid : Valid cutoff requests outcome initial := ⟨Nat.le_refl _, existing, fun worker => .inl (retained worker)⟩
  have safe : AllSafe (Valid cutoff requests outcome) (Grows cutoff) post (Simulation.State.initial initial start) :=
    ⟨valid, fun worker => fresh worker initial valid⟩
  obtain ⟨growth, kept, workers⟩ := Simulation.run_safe (valid := Valid cutoff requests outcome) (grows := Grows cutoff)
    (Grows.refl cutoff) (fun first second => first.trans second) start advance post fresh clock events safe executed
  exact ⟨growth.records, kept.2.2, fun worker returned finished =>
    (workers worker).returned (Grows.refl cutoff) kept finished⟩

end LeanCloud.Proofs.ConcurrentPublication
