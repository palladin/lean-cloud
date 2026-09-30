import LeanCloud.Proofs.ConcurrentRepeatedProgress

/-! Identify queue delivery at the actual atomic dequeue commit. A receipt may
expire before its saved reply is delivered; processing still uses that reply.
Fair delivery concerns these commits, not successful workflow processing. -/

namespace LeanCloud.Proofs.ConcurrentDelivery
open Lean LeanEff Simulation SimulationBackend ReplayRecovery ConcurrentAudit

/-- The existing backend's dequeue primitive, named for the trace predicate. -/
def dequeue (duration : Nat) (state : Durable) : Option (Location × LeaseQueueModel.Receipt) × Durable :=
  let (delivery, transport) := LeaseQueueModel.dequeue duration state.transport
  (delivery.map (fun d => (d.value, d.receipt)), { state with transport })

/-- The adapter's local continuation after a dequeue reply. No backend request
is introduced here; this just installs the received handle and calls the user. -/
def dispatch (next : Work → ExceptT CloudError (StateT SimulationBackend.Worker M) α)
    (reply : Option (Location × LeaseQueueModel.Receipt)) : M (Except CloudError α × SimulationBackend.Worker) :=
  match reply with
  | none => (next .idle).run ⟨(), none⟩
  | some (location, receipt) => (next (.item location)).run ⟨(), some (location, receipt)⟩

/-- Normalizing the actual poll preserves its two primitive requests and their
continuations. A completed-result reply skips dequeue, as in the real adapter. -/
theorem poll_equivalent (duration : Nat) (handle : SimulationBackend.Worker)
    (next : Work → ExceptT CloudError (StateT SimulationBackend.Worker M) α) :
    Equivalent ((do
      let work ← (queue duration).next
      next work : ExceptT CloudError (StateT SimulationBackend.Worker M) α).run handle)
      (do
        match ← SimM.atomic (fun state : Durable => (state.completed, state)) with
        | some outcome => (next (.completed outcome)).run ⟨(), none⟩
        | none => do
          let reply ← SimM.atomic (dequeue duration)
          dispatch next reply) := by
  rcases handle with ⟨⟨⟩, delivery⟩
  dsimp [queue, LeanCloud.LeaseQueue.toWorkQueue, LeanCloud.LeaseQueue.liftBackend,
    readCompleted, StateT.run, StateT.bind, StateT.pure, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, SimM.atomic, EffF.send, bind, pure,
    EffF.bind, ExceptT.run, ExceptT.bind, ExceptT.bindCont, liftM, monadLift, ExceptT.lift]
  apply Equivalent.request
  intro outcome
  simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, pure]
  cases outcome with
  | some outcome =>
    simp only [StateT.pure, pure, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind]
    exact .refl _
  | none =>
    dsimp [transport, StateT.run, StateT.bind, StateT.pure, SimM.atomic, EffF.send, bind, pure, EffF.bind]
    apply Equivalent.request
    intro reply
    simp only [ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, pure]
    cases reply with
    | none =>
      simp only [StateT.pure, pure, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind]
      exact .refl _
    | some pair =>
      cases pair
      simp only [StateT.modifyGet, StateT.bind, StateT.pure, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, bind, pure]
      exact .refl _

/-- A concrete successful dequeue by this caller. The continuation describes
the suspended code, not its eventual execution or a successful step result. -/
def Committed {start : Fin count → M (Except CloudError α × SimulationBackend.Worker)}
    {clock : Nat → Durable → Durable} (trace : Simulation.Schedule start clock)
    (duration : Nat) (next : Work → ExceptT CloudError (StateT SimulationBackend.Worker M) α)
    (n : Nat) (worker : Fin count) (delivery : LeaseQueueModel.Delivery Location) : Prop :=
  ∃ rest : ArrsF (Atomic Durable) (Option (Location × LeaseQueueModel.Receipt)) (Except CloudError α × SimulationBackend.Worker),
    trace.events n = some (.commit worker) ∧
    (trace.states n).workers worker = .waiting (dequeue duration) rest ∧
    (∀ reply, Equivalent (ArrsF.apply rest reply) (dispatch next reply)) ∧
    (LeaseQueueModel.dequeue duration (trace.states n).durable.transport).1 = some delivery

/-- Committing dequeue saves exactly the issued receipt and caller continuation.
The result is available before any resume event or workflow execution. -/
theorem Committed.saved {start : Fin count → M (Except CloudError α × SimulationBackend.Worker)}
    {clock : Nat → Durable → Durable} {trace : Simulation.Schedule start clock}
    {duration next n worker delivery} (committed : Committed trace duration next n worker delivery) :
    ∃ rest : ArrsF (Atomic Durable) (Option (Location × LeaseQueueModel.Receipt)) (Except CloudError α × SimulationBackend.Worker),
      (trace.states (n + 1)).workers worker = .responding (some (delivery.value, delivery.receipt)) rest ∧
      (∀ reply, Equivalent (ArrsF.apply rest reply) (dispatch next reply)) ∧
      (trace.states (n + 1)).durable = (dequeue duration (trace.states n).durable).2 := by
  obtain ⟨rest, event, waiting, caller, selected⟩ := committed
  have executed := trace.execution n _ event
  simp only [Simulation.step, waiting] at executed
  rw [← Except.ok.inj executed]
  refine ⟨rest, ?_, caller, rfl⟩
  simp only [State.setWorker_same, dequeue, selected, Option.map_some]

/-- The saved dequeue reply already identifies the selected code. Its route
is activated and its receipt matched a real message at this exact boundary;
neither fact requires the lease to remain current during later execution. -/
theorem Committed.enters {start : Fin count → M (Except CloudError α × SimulationBackend.Worker)}
    {clock : Nat → Durable → Durable} {trace : Simulation.Schedule start clock}
    {duration next n worker delivery tree} (committed : Committed trace duration next n worker delivery)
    (valid : ConcurrentQueue.Valid tree (trace.states n).durable) :
    (History.worker ((trace.states (n + 1)).workers worker)).Continues
      (History.program ((next (.item delivery.value)).run ⟨(), some (delivery.value, delivery.receipt)⟩)) ∧
    tree.Activated (ConcurrentJournal.view (trace.states (n + 1)).durable) delivery.value ∧
    ∃ message, LeaseQueueModel.current delivery.receipt (trace.states (n + 1)).durable.transport = some message ∧
      message.value = delivery.value := by
  obtain ⟨rest, saved, caller, durable⟩ := committed.saved
  obtain ⟨_, _, _, _, selected⟩ := committed
  refine ⟨?_, ?_, ?_⟩
  · rw [saved, History.worker]
    apply (Simulation.Worker.continues_responding _ _).equivalent
    rw [History.continuation_apply]
    exact (caller (some (delivery.value, delivery.receipt))).record
  · rw [durable]
    exact (valid.pending.dequeue duration).2 delivery selected
  · rw [durable]
    obtain ⟨message, present, value, _⟩ := LeaseQueue.dequeue_retains
      (Prod.ext selected rfl)
    exact ⟨message, present, value⟩

end LeanCloud.Proofs.ConcurrentDelivery

namespace LeanCloud.Proofs.ConcurrentRepeated
open Lean Simulation SimulationBackend ReplayRecovery ConcurrentAudit

/-- `afterPoll` is the real iteration's caller after the two queue primitives. -/
theorem iteration_poll_equivalent (duration traversal : Nat) (program : Cloud M Json) :
    Equivalent (rawIteration duration traversal program)
      (do
        match ← SimM.atomic (fun state : Durable => (state.completed, state)) with
        | some outcome => (afterPoll duration traversal program (.completed outcome)).run ⟨(), none⟩
        | none => do
          let reply ← SimM.atomic (ConcurrentDelivery.dequeue duration)
          ConcurrentDelivery.dispatch (afterPoll duration traversal program) reply) :=
  ConcurrentDelivery.poll_equivalent duration ⟨(), none⟩ (afterPoll duration traversal program)

/-- Retained work is eventually delivered by an actual poll, acknowledged,
or made unnecessary by durable completion. This includes eventual lease
availability; it assumes neither processing success nor a finite loop budget.
The caller in `Committed` is the normalized real iteration above. -/
def FairDelivery (trace : RawTrace duration traversal program count) : Prop :=
  ∀ (cut slot : Nat) (message : LeaseQueueModel.Message Location),
    (trace.states cut).durable.transport.messages[slot]? = some (some message) →
    ∃ n, cut ≤ n ∧
      ((trace.states n).durable.completed ≠ none ∨
       (trace.states n).durable.transport.messages[slot]? = some none ∨
       ∃ worker delivery, delivery.receipt.message = slot ∧
         ConcurrentDelivery.Committed trace.schedule duration (afterPoll duration traversal program) n worker delivery)

variable {program : Cloud M Json} {tree : ExecutionTree}
  (whole : Expansion program tree) (supported : PureProgram program)
  (comparable : Comparable (tree.journal Location.root))
  (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
  (duration traversal : Nat) (enough : sizeOf tree ≤ traversal)
  (trace : RawTrace duration traversal program count)
  (initialized : trace.states 0 = Simulation.State.initial SimulationBackend.initial
    (fun _ : Fin count => rawIteration duration traversal program))

include whole supported comparable sameExit enough initialized

/-- A real dequeue commit is enough to start the worker-progress argument.
The saved receipt can expire or be replaced while the reply waits; publication
is still derived from the caller's code and fair worker actions. -/
theorem dequeue_publishes (fair : trace.WeaklyFair) (worker : Fin count) (atTime : Nat)
    (noCrash : trace.NoCrashesAfter worker (atTime + 1)) (delivery : LeaseQueueModel.Delivery Location)
    (committed : ConcurrentDelivery.Committed trace.schedule duration
      (afterPoll duration traversal program) atTime worker delivery) :
    ∃ node, ∃ _route : TreeRoute tree Location.root delivery.value node,
      ∃ later response, atTime < later ∧
        PublishedStep tree delivery.value node ((recordTrace trace).states (atTime + 1)).durable
          response ((recordTrace trace).states later).durable ∧
        ∀ locations, response = .runnable locations → ∀ target ∈ locations,
          ∃ issuedAt, ∃ slot : Nat, ∃ message : LeaseQueueModel.Message Location, atTime < issuedAt ∧ issuedAt ≤ later ∧
            (trace.states issuedAt).durable.transport.messages[slot]? = some (some message) ∧ message.value = target := by
  obtain ⟨kept, _growth⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  obtain ⟨continuing, activated, present⟩ := committed.enters (kept atTime).1.1
  obtain ⟨node, route, active⟩ := activated
  have received : ConcurrentHandoff.Received delivery.value delivery.receipt
      ((recordTrace trace).states (atTime + 1)).durable := History.Seen.now present
  obtain ⟨later, response, after, published, successors⟩ := selected_publishes whole supported comparable sameExit
    duration traversal enough trace initialized fair worker (atTime + 1) noCrash
    delivery.value node route active delivery.receipt received continuing
  refine ⟨node, route, later, response, by omega, published, ?_⟩
  intro locations same target member
  obtain ⟨issuedAt, slot, message, newer, earlier, held, value⟩ := successors locations same target member
  exact ⟨issuedAt, slot, message, by omega, earlier, held, value⟩

/-- Separate the two ways a retained item makes progress after crashes stop:
an already-running delivery retires it, or a new dequeue leads to publication.
The retirement case is retained explicitly for historical publication accounting.
Fairness itself mentions only queue events, never this processing conclusion. -/
theorem fair_delivery (fair : trace.WeaklyFair) (deliveries : FairDelivery trace) (cut : Nat)
    (noCrash : ∀ worker, trace.NoCrashesAfter worker cut)
    (slot : Nat) (message : LeaseQueueModel.Message Location)
    (stored : (trace.states cut).durable.transport.messages[slot]? = some (some message)) :
    (∃ later, cut ≤ later ∧ (trace.states later).durable.completed = some tree.exit) ∨
    (∃ later, cut ≤ later ∧ (trace.states later).durable.transport.messages[slot]? = some none) ∨
    ∃ started node, ∃ _route : TreeRoute tree Location.root message.value node,
      ∃ later response, cut < started ∧ started ≤ later ∧
        PublishedStep tree message.value node ((recordTrace trace).states started).durable
          response ((recordTrace trace).states later).durable := by
  obtain ⟨kept, growth⟩ := raw_certified whole supported comparable sameExit duration traversal enough trace initialized
  obtain ⟨n, after, finished | removed | selected⟩ := deliveries cut slot message stored
  · left
    cases present : (trace.states n).durable.completed with
    | none => exact False.elim (finished present)
    | some outcome =>
      have correct := (kept n).1.1.completed outcome present
      exact ⟨n, after, present.trans (congrArg some correct)⟩
  · exact .inr (.inl ⟨n, after, removed⟩)
  · obtain ⟨worker, delivery, sameSlot, committed⟩ := selected
    obtain ⟨_, _, actual, present, sameValue⟩ := committed.enters (kept n).1.1
    have held := (LeaseQueue.current_iff.mp present).1
    rw [sameSlot] at held
    have inside := (Array.getElem?_eq_some_iff.mp stored).choose
    have lineage := (kept (n + 1)).1.2.1.lineage (growth cut (n + 1) (by omega)).2
    obtain ⟨previous, original, payload⟩ := lineage.retained slot actual inside held
    change (trace.states cut).durable.transport.messages[slot]? = some (some previous) at original
    rw [stored] at original
    cases original
    have samePayload : message.value = delivery.value := payload.trans sameValue
    obtain ⟨node, route, later, response, beyond, published, _⟩ := dequeue_publishes whole supported comparable sameExit
      duration traversal enough trace initialized fair worker n (fun index beyond => noCrash worker index (by omega)) delivery committed
    rw [← samePayload] at route published
    exact .inr (.inr ⟨n + 1, node, route, later, response, by omega, by omega, published⟩)

end LeanCloud.Proofs.ConcurrentRepeated
