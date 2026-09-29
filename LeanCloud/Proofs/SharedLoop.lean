import LeanCloud.Proofs.SharedCoverage

/-! One iteration of the actual replay loop, including polling and publication.
The factoring equation below connects this proof view to `run` itself. -/

namespace LeanCloud.Proofs.SharedRecovery
open Lean CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

/-- Proof view of one loop iteration. `none` continues the loop; `some` returns
the observed completion. This uses the actual worker and queue operations. -/
def iteration {m : Type → Type} [Monad m] (db : Db σ m) (blobs : BlobStorage σ m)
    (queue : WorkQueue σ m) (fuel : Nat) (source : Cloud m Json) :
    ExceptT CloudError (StateT σ m) (Option Exit) := do
  match ← queue.next with
  | .idle => pure none
  | .completed outcome => pure (some outcome)
  | .item location =>
    let response ← step db blobs fuel source location
    queue.complete location response
    pure (match response with | .done outcome => some outcome | .runnable _ => none)

/-- The public loop is exactly this iteration followed by its existing recursive
continuation. No different worker or recovery evaluator is assumed. -/
theorem run_succ_eq {m : Type → Type} [Monad m] [LawfulMonad m] [Codec α]
    (db : Db σ m) (blobs : BlobStorage σ m) (queue : WorkQueue σ m)
    (fuel : Nat) (source : Cloud m Json) :
    run (α := α) db blobs queue (fuel + 1) source = (do
      match ← iteration db blobs queue (fuel + 1) source with
      | some outcome => result outcome
      | none => run db blobs queue fuel source) := by
  rw [run]
  simp only [iteration, bind_assoc]
  congr 1
  funext work
  cases work with
  | idle => simp only [pure_bind]
  | completed outcome => simp only [pure_bind]
  | item location =>
    simp only [bind_assoc]
    congr 1
    funext response
    cases response <;> simp only [pure_bind]

theorem iteration_eq {m : Type → Type} [Monad m] [LawfulMonad m]
    (db : Db σ m) (blobs : BlobStorage σ m) (queue : WorkQueue σ m)
    (fuel : Nat) (source : Cloud m Json) (worker : σ) :
    (iteration db blobs queue fuel source).run worker = (do
      let (work, worker) ← queue.next worker
      match work with
      | .idle => pure (.ok none, worker)
      | .completed outcome => pure (.ok (some outcome), worker)
      | .item location =>
        (fun returned => (returned.1.map (fun response =>
          match response with | .done outcome => some outcome | .runnable _ => none), returned.2)) <$>
          ((do
            let response ← step db blobs fuel source location
            queue.complete location response
            pure response : ExceptT CloudError (StateT σ m) StepResult).run worker)) := by
  simp only [iteration, bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, StateT.bind,
    liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, pure,
    ExceptT.pure, Functor.map, StateT.map, bind_assoc, pure_bind]
  congr 1
  funext (work, worker)
  cases work with
  | idle => rfl
  | completed outcome => rfl
  | item location =>
    simp only [StateT.bind, ← bind_pure_comp, bind_assoc]
    congr 1
    funext (outcome, worker)
    cases outcome <;> simp [ExceptT.bindCont, StateT.bind, StateT.map, StateT.pure,
      pure, Except.map]

/-- Polling derives a current receipt; executing and publishing that delivery
retains all unfinished work. The conjunction holds at every crash boundary,
not just at the beginning and end of successful iterations. -/
theorem iteration_covered {source : Cloud (CrashModel.M Journal) Json} {tree}
    (expansion : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (blobs : BlobStorage Worker M)
    (worker : Worker) (fuel : Nat) (enough : sizeOf tree ≤ fuel) (lower : Journal) :
    Triple (fun state => Extends lower state.1 ∧ Valid tree state ∧ Covered tree state)
      ((iteration workerDb blobs queue fuel (journalMap.program source)).run worker)
      (fun returned state => ∃ completed, returned = (.ok completed, (⟨(), none⟩ : Worker)) ∧
        (Extends lower state.1 ∧ Valid tree state ∧ Covered tree state) ∧ ∀ outcome, completed = some outcome → outcome = tree.exit)
      (fun state => Extends lower state.1 ∧ Valid tree state ∧ Covered tree state) := by
  rw [iteration_eq]
  have polled := ((next_spec expansion worker).conjoin (next_covered tree worker)).weaken
    (pre' := fun state => Extends lower state.1 ∧ Valid tree state ∧ Covered tree state)
    (fun _ h => h.2) (fun _ _ h => h) (fun _ h => h)
  have growth : ∀ start : State Durable, (Extends lower start.durable.1 ∧ Valid tree start.durable ∧ Covered tree start.durable) →
      Extends lower (queue.next worker |>.run start).2.durable.1 := by
    intro start kept
    rw [queue_next]
    exact kept.1
  apply ((polled.ensure growth).weaken (fun _ h => h) (fun _ _ h => h)
    (fun _ h => ⟨h.2, h.1⟩)).bind
  intro returned
  rcases returned with ⟨work, ⟨handle, delivery⟩⟩
  cases handle
  cases work with
  | idle =>
    apply (Triple.pure _ _).weaken (fun _ h => h) _ (fun _ h => h)
    intro returned state h
    obtain ⟨rfl, ⟨⟨valid, polled, _⟩, covered⟩, growth⟩ := h
    have cleared : delivery = none := polled.2
    subst delivery
    exact ⟨none, rfl, ⟨growth, valid, covered⟩, by simp⟩
  | completed outcome =>
    apply (Triple.pure _ _).weaken (fun _ h => h) _ (fun _ h => h)
    intro returned state h
    obtain ⟨rfl, ⟨⟨valid, polled, _⟩, covered⟩, growth⟩ := h
    obtain ⟨correct, _, cleared⟩ := polled.2
    change delivery = none at cleared
    subst delivery
    exact ⟨some outcome, rfl, ⟨growth, valid, covered⟩, by intro value same; cases same; exact correct⟩
  | item location =>
    intro current h
    obtain ⟨⟨⟨valid, polled, ready⟩, covered⟩, growth⟩ := h
    obtain ⟨node, route, activated, _⟩ := ready location rfl
    obtain ⟨_, receipt, message, delivered, held, payload⟩ := polled.2
    change delivery = some (location, receipt) at delivered
    subst delivery
    have processed := step_complete_covered expansion supported route current.durable valid covered activated held payload
      comparable (sameExit location node route.member) blobs fuel
      (Nat.le_trans route.fuel_bound enough)
    apply (processed.map (fun returned => (returned.1.map (fun response =>
      match response with | .done outcome => some outcome | .runnable _ => none), returned.2))).weaken
      (pre' := (· = current.durable))
      (post' := fun returned state => ∃ completed, returned = (.ok completed, (⟨(), none⟩ : Worker)) ∧
        (Extends lower state.1 ∧ Valid tree state ∧ Covered tree state) ∧ ∀ outcome, completed = some outcome → outcome = tree.exit)
      (stopped' := fun state => Extends lower state.1 ∧ Valid tree state ∧ Covered tree state)
      (fun _ h => h) _ (fun _ h => ⟨growth.trans h.1, h.2⟩) current rfl
    intro returned state h
    obtain ⟨value, rfl, response, rfl, ⟨advanced, validFinal⟩, emits⟩ := h
    cases response with
    | done outcome => exact ⟨some outcome, rfl, ⟨growth.trans advanced, validFinal⟩, by intro value same; cases same; exact emits⟩
    | runnable locations => exact ⟨none, rfl, ⟨growth.trans advanced, validFinal⟩, by simp⟩

end LeanCloud.Proofs.SharedRecovery
