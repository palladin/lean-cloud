import LeanCloud.Proofs.ConcurrentTransfer
import LeanCloud.Proofs.ReplayIteration

/-! The existing one-iteration proof view uses the actual poll, step, and
publication calls. Factoring it out of the replay loop preserves every atomic
request and saved reply; no monad-law instance for freer syntax is assumed. -/

namespace LeanCloud.Proofs.ReplayIteration
open Lean Simulation ReplayInterpreter.Internal

/-- More traversal fuel preserves one polling iteration up to its own
interpreter error. Workflow failures remain successful `some Exit` results. -/
theorem iteration_truncates (db : Db σ (SimM δ)) (blobs : BlobStorage σ (SimM δ))
    (queue : WorkQueue σ (SimM δ)) (program : Cloud (SimM δ) Json) (supported : PureProgram program)
    (fuel extra : Nat) : Truncates ConcurrentQueue.exhausted
      (iteration db blobs queue fuel program) (iteration db blobs queue (fuel + extra) program) := by
  unfold iteration
  apply Truncates.bind (Truncates.refl _ _)
  intro work
  cases work with
  | idle | completed outcome => exact Truncates.refl _ _
  | item location =>
    apply Truncates.bind (ConcurrentQueue.step_truncates db blobs program supported location fuel extra)
    intro response
    apply Truncates.bind (Truncates.refl _ _)
    intro _
    exact Truncates.refl _ _

theorem run_succ_equivalent [Codec α] (db : Db σ (SimM δ)) (blobs : BlobStorage σ (SimM δ))
    (queue : WorkQueue σ (SimM δ)) (fuel : Nat) (program : Cloud (SimM δ) Json) (handle : σ) :
    Equivalent ((run (α := α) db blobs queue (fuel + 1) program).run handle)
      ((do
        match ← iteration db blobs queue (fuel + 1) program with
        | some outcome => result outcome
        | none => run db blobs queue fuel program).run handle) := by
  rw [ReplayInterpreter.Internal.run]
  unfold iteration
  apply Equivalent.symm
  apply (Equivalent.action_bind_assoc (liftM queue.next) _ _ handle).trans
  apply Equivalent.action_bind (fun _ => .refl _)
  intro work handle
  cases work with
  | idle | completed outcome => exact .refl _
  | item location =>
    apply (Equivalent.action_bind_assoc (step db blobs (fuel + 1) program location) _ _ handle).trans
    apply Equivalent.action_bind (fun _ => .refl _)
    intro response handle
    apply (Equivalent.action_bind_assoc (liftM (queue.complete location response)) _ _ handle).trans
    apply Equivalent.action_bind (fun _ => .refl _)
    intro _ handle
    cases response <;> exact .refl _

end LeanCloud.Proofs.ReplayIteration

namespace LeanCloud.Proofs.ConcurrentAudit
open Lean LeanEff Simulation SimulationBackend ReplayRecovery

/-- An iteration started after durable completion only reads that outcome.
This small progress proof exposes its actual read and saved-reply boundaries;
it needs no traversal budget because no workflow step is executed. -/
theorem iteration_completed {tree : ExecutionTree} (duration fuel : Nat) (program : Cloud M Json)
    (handle : SimulationBackend.Worker) (initial : ConcurrentHandoff.Log) (outcome : Exit)
    (completed : initial.current.completed = some outcome) :
    Reaches (Valid tree) Grows
      (fun worker _ => worker = .finished (.ok (some outcome), (⟨(), none⟩ : SimulationBackend.Worker)))
      (.ofProgram (History.program ((ReplayIteration.iteration SimulationBackend.db SimulationBackend.noBlobs
        (queue duration) fuel program).run handle))) initial := by
  rcases handle with ⟨⟨⟩, delivery⟩
  dsimp [ReplayIteration.iteration, queue, LeanCloud.LeaseQueue.toWorkQueue, LeanCloud.LeaseQueue.liftBackend,
    readCompleted, StateT.run, StateT.bind, StateT.pure, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, SimM.atomic, EffF.send, bind, pure,
    EffF.bind, History.program, History.continuation, Simulation.Worker.ofProgram,
    ExceptT.run, ExceptT.bind, ExceptT.bindCont, liftM, monadLift, ExceptT.lift]
  apply Reaches.waiting
  intro observed valid growth
  apply Reaches.responding
  intro delivered kept later
  simp only [History.continuation, ArrsF.apply, ArrsF.viewL, ArrsF.viewLAppend, EffF.bind, History.operation,
    growth.1.completed outcome completed, pure, StateT.pure, ExceptT.pure,
    History.program, Simulation.Worker.ofProgram]
  exact .arrived fun _ _ _ => rfl

/-- Adequate traversal fuel makes a complete polling iteration return without
an interpreter error. A `some` response is the durable final result; `none`
continues the loop. Even an idle iteration crosses a real backend boundary. -/
theorem iteration_safe {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration fuel : Nat) (enough : sizeOf tree ≤ fuel) (handle : SimulationBackend.Worker)
    (initial : ConcurrentHandoff.Log) (valid : Valid tree initial) :
    Safe (Valid tree) Grows (fun returned final => ∃ outcome,
      returned = (.ok outcome, (⟨(), none⟩ : SimulationBackend.Worker)) ∧
      initial.past.length < final.past.length ∧
      ∀ value, outcome = some value → value = tree.exit ∧ final.current.completed = some value)
      (.ofProgram (History.program ((ReplayIteration.iteration SimulationBackend.db SimulationBackend.noBlobs
        (queue duration) fuel program).run handle))) initial := by
  unfold ReplayIteration.iteration
  change Safe _ _ _ (.ofProgram (History.program ((liftM (queue duration).next :
    ExceptT CloudError (StateT SimulationBackend.Worker M) Work).run handle >>= _))) initial
  rw [History.program_bind]
  apply Safe.bind Grows.refl (fun a b => a.trans b) (poll_safe tree duration handle initial valid) valid
  intro returned polled kept done
  obtain ⟨work, same, next, received, advanced⟩ := done
  rcases returned with ⟨outcome, handle⟩
  dsimp only at same
  subst outcome
  cases work with
  | idle =>
    cases handle with
    | mk backend delivery =>
      cases backend
      change delivery = none at next
      subst delivery
      exact .finished fun final finalValid later => ⟨none, rfl, Nat.lt_of_lt_of_le advanced later.2.length, by simp⟩
  | completed outcome =>
    obtain ⟨cleared, correct, stored⟩ := next
    cases handle with
    | mk backend delivery =>
      cases backend
      change delivery = none at cleared
      subst delivery
      apply Safe.finished
      intro final finalValid later
      refine ⟨some outcome, rfl, Nat.lt_of_lt_of_le advanced later.2.length, ?_⟩
      intro value same
      cases same
      exact ⟨correct, later.1.completed outcome stored⟩
  | item location =>
    obtain ⟨receipt, delivered, node, route, active⟩ := next
    obtain ⟨observed, delivery, received⟩ := received
    rw [delivered] at delivery
    cases delivery
    cases handle with
    | mk backend delivery =>
      cases backend
      change delivery = some (location, receipt) at delivered
      subst delivery
      let first := ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs fuel program location
      let finish := fun response => (liftM ((queue duration).complete location response) :
        ExceptT CloudError (StateT SimulationBackend.Worker M) Unit)
      let processed := do let response ← first; finish response; pure response
      let next := fun response => (pure (match response with
        | StepResult.done outcome => some outcome
        | .runnable _ => none) : ExceptT CloudError (StateT SimulationBackend.Worker M) (Option Exit))
      let handle : SimulationBackend.Worker := ⟨(), some (location, receipt)⟩
      have safe := delivered_safe whole supported route comparable (sameExit _ _ route.member)
        duration fuel (Nat.le_trans route.fuel_bound enough) receipt polled kept active received
      have grouped : Safe (Valid tree) Grows (fun returned final => ∃ outcome,
          returned = (.ok outcome, (⟨(), none⟩ : SimulationBackend.Worker)) ∧
          initial.past.length < final.past.length ∧
          ∀ value, outcome = some value → value = tree.exit ∧ final.current.completed = some value)
          (.ofProgram (History.program ((processed >>= next).run handle))) polled := by
        change Safe _ _ _ (.ofProgram (History.program (processed.run handle >>= _))) polled
        rw [History.program_bind]
        apply Safe.bind Grows.refl (fun a b => a.trans b) safe kept
        intro returned final finalValid done
        obtain ⟨response, rfl, executed, started, finished, progress, emitted, published⟩ := done
        apply Safe.finished
        intro last lastValid later
        refine ⟨_, rfl, Nat.lt_of_lt_of_le advanced (started.trans (finished.trans later)).2.length, ?_⟩
        cases response with
        | runnable locations => simp
        | done outcome =>
          intro value same
          cases same
          refine ⟨emitted, ?_⟩
          exact lastValid.published_done later.2 published
      exact grouped.equivalent Grows.refl (fun a b => a.trans b) kept
        (Equivalent.action_retain first finish next handle).record

/-- One iteration of the original loop reaches its actual recursive or result
continuation under fair worker scheduling. Its traversal budget is explicit;
this does not assume that finitely many iterations complete the workflow. -/
theorem run_iteration [Codec α]
    {start : Fin count → M (Except CloudError α × SimulationBackend.Worker)}
    {clock : Nat → Durable → Durable} (trace : Simulation.Trace start clock)
    {program : Cloud M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration remaining : Nat) (enough : sizeOf tree ≤ remaining + 1)
    (kept : ∀ n, Valid tree ((History.trace trace).states n).durable)
    (growth : ∀ before after, before ≤ after →
      Grows ((History.trace trace).states before).durable ((History.trace trace).states after).durable)
    (fair : trace.WeaklyFair) (worker : Fin count) (atTime : Nat)
    (noCrash : trace.NoCrashesAfter worker atTime) (handle : SimulationBackend.Worker)
    (continuing : (((History.trace trace).states atTime).workers worker).Continues
      (History.program ((ReplayInterpreter.Internal.run SimulationBackend.db SimulationBackend.noBlobs
        (queue duration) (remaining + 1) program).run handle))) :
    let next : Option Exit → ExceptT CloudError (StateT SimulationBackend.Worker M) α := fun outcome =>
      match outcome with
      | some value => ReplayInterpreter.Internal.result value
      | none => ReplayInterpreter.Internal.run SimulationBackend.db SimulationBackend.noBlobs (queue duration) remaining program
    ∃ later outcome, atTime < later ∧
      (((History.trace trace).states later).workers worker).Continues
        (History.program ((next outcome).run ⟨(), none⟩)) ∧
      ∀ value, outcome = some value → value = tree.exit ∧ (trace.states later).durable.completed = some value := by
  let next : Option Exit → ExceptT CloudError (StateT SimulationBackend.Worker M) α := fun outcome =>
    match outcome with
    | some value => ReplayInterpreter.Internal.result value
    | none => ReplayInterpreter.Internal.run SimulationBackend.db SimulationBackend.noBlobs (queue duration) remaining program
  let action := ReplayIteration.iteration SimulationBackend.db SimulationBackend.noBlobs (queue duration) (remaining + 1) program
  let resume := fun returned : Except CloudError (Option Exit) × SimulationBackend.Worker =>
    History.program (ExceptT.bindCont next returned.1 returned.2)
  have same : (((History.trace trace).states atTime).workers worker).Continues
      (History.program (action.run handle) >>= resume) := by
    have factored := continuing.equivalent (ReplayIteration.run_succ_equivalent SimulationBackend.db
      SimulationBackend.noBlobs (queue duration) remaining program handle).record
    change Worker.Continues _ (History.program (action.run handle >>= _)) at factored
    rwa [History.program_bind] at factored
  have safe := iteration_safe whole supported comparable sameExit duration (remaining + 1) enough handle
    ((History.trace trace).states atTime).durable (kept atTime)
  have progress := safe.reaches_continuation Grows.refl (fun a b => a.trans b) (kept atTime) resume _ same
  obtain ⟨later, after, returned, remainingCode, outcome, sameResult, advanced, correct⟩ :=
    (History.trace trace).eventually_reaches (History.trace_fair trace fair) worker
      Grows.refl (fun a b => a.trans b) kept growth progress atTime rfl
      (History.trace_noCrashes trace worker atTime noCrash) (.refl _)
  subst returned
  have strictly : atTime < later := by
    by_cases same : atTime = later
    · subst later; exact False.elim (Nat.lt_irrefl _ advanced)
    · omega
  exact ⟨later, outcome, strictly, remainingCode, correct⟩

end LeanCloud.Proofs.ConcurrentAudit
