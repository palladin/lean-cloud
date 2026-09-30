import LeanCloud.Proofs.LeasedStep
import LeanCloud.Proofs.LeaseQueue
import Init.Data.Array.Monadic

/-! Queue safety for the actual worker adapter. Retained messages may be leased,
redelivered, acknowledged or consumed by other workers between calls. The
invariant records their meaning, not a fixed set of publication requests. -/

namespace LeanCloud.Proofs.ConcurrentQueue
open Lean LeanEff Simulation SimulationBackend LeaseQueueModel

structure Valid (tree : ExecutionTree) (state : Durable) : Prop where
  journal : ConcurrentJournal.Valid (tree.journal Location.root) state
  pending : LeaseQueue.Values (tree.Activated (ConcurrentJournal.view state)) state.transport
  completed : ∀ outcome, state.completed = some outcome → outcome = tree.exit

/-- Journal growth and a persistent final result. Messages may be added,
leased or removed; no assumption freezes successors while they are consumed. -/
structure Grows (before after : Durable) : Prop where
  journal : ConcurrentJournal.Grows before after
  completed : ∀ outcome, before.completed = some outcome → after.completed = some outcome

theorem Grows.refl (state : Durable) : Grows state state := ⟨.refl _, fun _ stored => stored⟩

theorem Grows.trans {before middle after : Durable} (first : Grows before middle) (last : Grows middle after) :
    Grows before after := ⟨first.journal.trans last.journal, fun value stored => last.completed value (first.completed value stored)⟩

theorem Valid.initial (tree : ExecutionTree) : Valid tree SimulationBackend.initial := by
  constructor
  · intro key value stored
    simp [ConcurrentJournal.view, SimulationBackend.initial] at stored
  · apply LeaseQueue.Values.enqueue
    · intro index message stored
      simp at stored
    · exact ExecutionTree.Activated.root tree _
  · intro outcome stored
    cases stored

theorem Valid.advance {tree state} (valid : Valid tree state) (elapsed : Nat) :
    Valid tree (SimulationBackend.advance elapsed state) := ⟨valid.journal, valid.pending, valid.completed⟩

theorem Grows.advance (elapsed : Nat) (state : Durable) :
    Grows state (SimulationBackend.advance elapsed state) := ⟨.refl _, fun _ stored => stored⟩

private def enqueued (location : Location) (state : Durable) : Durable :=
  { state with transport := (LeaseQueueModel.enqueue location state.transport).2 }

private def polled (duration : Nat) (state : Durable) : Durable :=
  { state with transport := (LeaseQueueModel.dequeue duration state.transport).2 }

private def acknowledged (receipt : Receipt) (state : Durable) : Durable :=
  { state with transport := (LeaseQueueModel.acknowledge receipt state.transport).2 }

private theorem enqueue_valid {tree state location} (valid : Valid tree state)
    (active : tree.Activated (ConcurrentJournal.view state) location) : Valid tree (enqueued location state) :=
  ⟨valid.journal, valid.pending.enqueue active, valid.completed⟩

private theorem poll_valid {tree state} (valid : Valid tree state) (duration : Nat) :
    Valid tree (polled duration state) :=
  ⟨valid.journal, (valid.pending.dequeue duration).1, valid.completed⟩

private theorem ack_valid {tree state} (valid : Valid tree state) (receipt : Receipt) :
    Valid tree (acknowledged receipt state) :=
  ⟨valid.journal, valid.pending.acknowledge receipt, valid.completed⟩

private theorem enqueue_safe {tree location} (duration : Nat) (worker : SimulationBackend.Worker)
    (state : Durable) (active : tree.Activated (ConcurrentJournal.view state) location) :
    Safe (Valid tree) Grows (fun returned _ => returned = ((), worker))
      (.ofProgram ((LeanCloud.LeaseQueue.liftBackend ((transport duration).enqueue location)).run worker)) state := by
  dsimp [LeanCloud.LeaseQueue.liftBackend, transport, StateT.run, SimM.atomic, EffF.send,
    bind, pure, EffF.bind, Simulation.Worker.ofProgram]
  apply Safe.waiting
  · intro current valid growth
    exact ⟨enqueue_valid valid (active.grow growth.journal.1), .refl _, fun _ stored => stored⟩
  · intro committed valid growth
    apply Safe.responding
    intro delivered deliveredValid later
    simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, Simulation.Worker.ofProgram]
    apply Safe.finished
    intro final finalValid last
    cases worker with | mk backend delivery => cases backend; rfl

private theorem done_safe (tree : ExecutionTree) (worker : SimulationBackend.Worker) (state : Durable) :
    Safe (Valid tree) Grows
      (fun returned final => returned = ((), worker) ∧ final.completed = some tree.exit)
      (.ofProgram ((LeanCloud.LeaseQueue.liftBackend (writeCompleted tree.exit)).run worker)) state := by
  dsimp [LeanCloud.LeaseQueue.liftBackend, writeCompleted, StateT.run, SimM.atomic, EffF.send,
    bind, pure, EffF.bind, Simulation.Worker.ofProgram]
  apply Safe.waiting
  · intro current valid growth
    refine ⟨⟨valid.journal, valid.pending, ?_⟩, .refl _, ?_⟩
    · intro outcome stored; exact (Option.some.inj stored).symm
    · intro outcome stored; exact congrArg some (valid.completed outcome stored).symm
  · intro committed valid growth
    apply Safe.responding
    intro delivered deliveredValid later
    simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, Simulation.Worker.ofProgram]
    apply Safe.finished
    intro final finalValid last
    exact ⟨by cases worker with | mk backend delivery => cases backend; rfl,
      (later.trans last).completed tree.exit rfl⟩

private theorem ack_safe (tree : ExecutionTree) (duration : Nat) (receipt : Receipt)
    (worker : SimulationBackend.Worker) (state : Durable) :
    Safe (Valid tree) Grows (fun returned _ => returned.2 = worker)
      (.ofProgram ((LeanCloud.LeaseQueue.liftBackend ((transport duration).acknowledge receipt)).run worker)) state := by
  dsimp [LeanCloud.LeaseQueue.liftBackend, transport, StateT.run, SimM.atomic, EffF.send,
    bind, pure, EffF.bind, Simulation.Worker.ofProgram]
  apply Safe.waiting
  · intro current valid growth
    exact ⟨ack_valid valid receipt, .refl _, fun _ stored => stored⟩
  · intro committed valid growth
    apply Safe.responding
    intro delivered deliveredValid later
    simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, Simulation.Worker.ofProgram]
    apply Safe.finished
    intro final finalValid last
    cases worker with | mk backend delivery => cases backend; rfl

private theorem state_bind {tree : ExecutionTree}
    {action : StateT SimulationBackend.Worker M α} {next : α → StateT SimulationBackend.Worker M β}
    {first : (α × SimulationBackend.Worker) → Durable → Prop}
    {post : (β × SimulationBackend.Worker) → Durable → Prop} {worker : SimulationBackend.Worker} {state : Durable}
    (safe : Safe (Valid tree) Grows first (.ofProgram (action.run worker)) state) (valid : Valid tree state)
    (resume : ∀ returned current, Valid tree current → Grows state current → first returned current →
      Safe (Valid tree) Grows post (.ofProgram ((next returned.1).run returned.2)) current) :
    Safe (Valid tree) Grows post (.ofProgram ((action >>= next).run worker)) state := by
  apply Safe.bind Grows.refl (fun first last => first.trans last)
    (safe.remember (fun first last => first.trans last) state (.refl _)) valid
  intro returned current kept h
  exact resume returned current kept h.1 h.2

/-- A delivered receipt may already be stale when its reply arrives. Its
location remains activated, and a reported final result remains durable. -/
def Next (tree : ExecutionTree) (returned : Work × SimulationBackend.Worker) (state : Durable) : Prop :=
  match returned.1 with
  | .idle => returned.2.delivery = none
  | .completed outcome => returned.2.delivery = none ∧ outcome = tree.exit ∧ state.completed = some outcome
  | .item location => ∃ receipt, returned.2.delivery = some (location, receipt) ∧
      tree.Activated (ConcurrentJournal.view state) location

/-- The actual adapter clears any previous receipt before polling, and only
returns activated work or the original program's final outcome. -/
theorem next_safe (tree : ExecutionTree) (duration : Nat) (worker : SimulationBackend.Worker)
    (state : Durable) :
    Safe (Valid tree) Grows (Next tree) (.ofProgram ((queue duration).next.run worker)) state := by
  dsimp [queue, LeanCloud.LeaseQueue.toWorkQueue, LeanCloud.LeaseQueue.liftBackend,
    readCompleted, transport, StateT.run, StateT.bind, StateT.pure, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, SimM.atomic, EffF.send, bind, pure,
    EffF.bind, Simulation.Worker.ofProgram]
  apply Safe.waiting
  · intro current kept growth
    exact ⟨kept, .refl _⟩
  · intro observed kept growth
    apply Safe.responding
    intro delivered deliveredValid later
    simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind]
    cases completed : observed.completed with
    | some outcome =>
      simp only [pure, StateT.pure, Simulation.Worker.ofProgram]
      apply Safe.finished
      intro final finalValid last
      exact ⟨rfl, kept.completed outcome completed, (later.trans last).completed outcome completed⟩
    | none =>
      simp only [Simulation.Worker.ofProgram]
      apply Safe.waiting
      · intro current valid growth
        exact ⟨poll_valid valid duration, .refl _, fun _ stored => stored⟩
      · intro polled valid growth
        apply Safe.responding
        intro received receivedValid extended
        simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind]
        cases selected : (LeaseQueueModel.dequeue duration polled.transport).1 with
        | none =>
          simp only [Option.map_none, ArrsF.apply, ArrsF.viewL, pure, StateT.pure, Simulation.Worker.ofProgram]
          exact .finished fun _ _ _ => rfl
        | some delivery =>
          simp only [Option.map_some, ArrsF.apply, ArrsF.viewL, bind, pure, StateT.bind, StateT.pure,
            StateT.modifyGet, EffF.bind,
            Simulation.Worker.ofProgram]
          apply Safe.finished
          intro final finalValid last
          exact ⟨delivery.receipt, rfl,
            ((valid.pending.dequeue duration).2 delivery selected).grow (extended.trans last).journal.1⟩

private abbrev enqueueBody (duration : Nat) (location : Location) (_ : PUnit.{1}) :
    StateT SimulationBackend.Worker M (ForInStep PUnit.{1}) := do
  LeanCloud.LeaseQueue.liftBackend ((transport duration).enqueue location)
  pure (.yield PUnit.unit)

private theorem enqueue_list_safe {tree : ExecutionTree} (duration : Nat) (locations : List Location)
    (worker : SimulationBackend.Worker) (state : Durable) (valid : Valid tree state)
    (active : ∀ location ∈ locations, tree.Activated (ConcurrentJournal.view state) location) :
    Safe (Valid tree) Grows (fun returned _ => returned = (PUnit.unit, worker))
      (.ofProgram ((forIn locations PUnit.unit (enqueueBody duration)).run worker)) state := by
  induction locations generalizing worker state with
  | nil => exact .finished fun _ _ _ => rfl
  | cons location rest ih =>
    rw [List.forIn_cons]
    have first : Safe (Valid tree) Grows (fun returned _ => returned = (.yield PUnit.unit, worker))
        (.ofProgram ((enqueueBody duration location PUnit.unit).run worker)) state := by
      unfold enqueueBody
      apply state_bind (enqueue_safe duration worker state (active location (by simp))) valid
      intro returned current kept growth same
      subst returned
      exact .finished fun _ _ _ => rfl
    apply state_bind first valid
    intro returned current kept growth same
    subst returned
    exact ih worker current kept (fun item member => (active item (by simp [member])).grow growth.journal.1)

/-- Completion persists a final result when present. Runnable successors can
already have been consumed, so no snapshot of queue contents is required. -/
def FinalStored (response : StepResult) (state : Durable) : Prop :=
  match response with
  | .done outcome => state.completed = some outcome
  | .runnable _ => True

private theorem FinalStored.grow {response before after} (published : FinalStored response before)
    (growth : Grows before after) : FinalStored response after := by
  cases response with
  | done outcome => exact growth.completed outcome published
  | runnable _ => trivial

/-- Actual publication and acknowledgement with an acquired receipt, including
partial publication and stale acknowledgements. All enqueued work retains its
original replay prerequisites. This safety theorem does not assert no-loss
coverage or eventual delivery. -/
theorem complete_safe {tree : ExecutionTree} (duration : Nat) (location : Location)
    (receipt : Receipt) (response : StepResult) (state : Durable) (valid : Valid tree state)
    (emitted : ConcurrentJournal.Emits tree response state) :
    Safe (Valid tree) Grows
      (fun returned final => returned = ((), (⟨(), none⟩ : SimulationBackend.Worker)) ∧ FinalStored response final)
      (.ofProgram (((queue duration).complete location response).run ⟨(), some (location, receipt)⟩)) state := by
  let worker : SimulationBackend.Worker := ⟨(), some (location, receipt)⟩
  have acknowledge (current : Durable) (kept : Valid tree current) (published : FinalStored response current) :
      Safe (Valid tree) Grows
        (fun returned final => returned = ((), (⟨(), none⟩ : SimulationBackend.Worker)) ∧ FinalStored response final)
        (.ofProgram ((do
          let _ ← LeanCloud.LeaseQueue.liftBackend ((transport duration).acknowledge receipt)
          modify fun worker : SimulationBackend.Worker => { worker with delivery := none }).run worker)) current := by
    apply state_bind (ack_safe tree duration receipt worker current) kept
    intro returned delivered deliveredValid later same
    rcases returned with ⟨accepted, handle⟩
    dsimp only at same
    subst handle
    exact .finished fun final finalValid last => ⟨rfl, published.grow (later.trans last)⟩
  dsimp [queue, LeanCloud.LeaseQueue.toWorkQueue, StateT.run, StateT.bind, MonadState.get, getThe, MonadStateOf.get,
    StateT.get, bind, pure, EffF.bind]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  change Safe _ _ _ (.ofProgram ((do
    match response with
    | .runnable locations => for location in locations do
        LeanCloud.LeaseQueue.liftBackend ((transport duration).enqueue location)
    | .done result => LeanCloud.LeaseQueue.liftBackend (writeCompleted result)
    let _ ← LeanCloud.LeaseQueue.liftBackend ((transport duration).acknowledge receipt)
    modify fun worker : SimulationBackend.Worker => { worker with delivery := none }).run worker)) state
  cases response with
  | done outcome =>
    change outcome = tree.exit at emitted
    subst outcome
    apply state_bind (done_safe tree worker state) valid
    intro returned current kept growth h
    obtain ⟨rfl, published⟩ := h
    exact acknowledge current kept published
  | runnable locations =>
    dsimp only
    rw [← Array.forIn_toList]
    apply state_bind (enqueue_list_safe duration locations.toList worker state valid
      (fun item member => emitted item (by simpa using member))) valid
    intro returned current kept growth same
    subst returned
    exact acknowledge current kept trivial

end LeanCloud.Proofs.ConcurrentQueue
