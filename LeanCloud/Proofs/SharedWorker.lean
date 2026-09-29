import LeanCloud.Proofs.SharedRecovery
import LeanCloud.Proofs.TreeTargetStep
import LeanCloud.Proofs.WorkerMap

/-! The actual replay worker, including its lease-receipt handle, over the
shared journal/queue crash state. No alternative worker evaluator is introduced. -/

namespace LeanCloud.Proofs.SharedRecovery
open Lean CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

def workerDb : Db Worker M := LeanCloud.LeaseQueue.db db

def workerMap : DbMap ReplayRecovery.db workerDb where
  actions := (journalMap.state Unit).comp (DbMap.leased (ρ := LeaseQueueModel.Receipt) db).actions
  get key := by
    change LeanCloud.LeaseQueue.liftBackend ((journalMap.db ReplayRecovery.db).get key) =
      LeanCloud.LeaseQueue.liftBackend (db.get key)
    rw [← db_eq]
  put key value := by
    change LeanCloud.LeaseQueue.liftBackend ((journalMap.db ReplayRecovery.db).put key value) =
      LeanCloud.LeaseQueue.liftBackend (db.put key value)
    rw [← db_eq]

/-- Adding the worker handle retains its receipt throughout journal operations.
A crash still escapes through the base monad with all committed data retained. -/
theorem worker_call_map (action : ReplayRecovery.Worker α) (worker : Worker) :
    (workerMap.worker.map action).run worker =
      (fun outcome => (outcome, worker)) <$> withLeft (ReplayRecovery.call action) := by
  obtain ⟨handle, receipt⟩ := worker
  cases handle
  change (do
    let pair ← journalMap.map (action.run ())
    pure (pair.1, (⟨(), receipt⟩ : Worker))) =
    (fun outcome => (outcome, (⟨(), receipt⟩ : Worker))) <$> journalMap.map (Prod.fst <$> action.run ())
  rw [journalMap.map_functor]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]

theorem step_eq (blobs : BlobStorage Worker M)
    (fuel : Nat) (source : Cloud (CrashModel.M Journal) Json) (supported : PureProgram source)
    (location : Location) (worker : Worker) :
    (step workerDb blobs fuel (journalMap.program source) location).run worker =
      (fun outcome => (outcome, worker)) <$>
        withLeft (ReplayRecovery.call (step ReplayRecovery.db noBlobs fuel source location)) := by
  rw [← workerMap.step_map journalMap noBlobs blobs fuel source supported location]
  exact worker_call_map _ worker

/-- The complete actual step preserves the joint invariant and the local lease
receipt. Emitted successors have durable reconstruction paths in the final Db. -/
theorem step_spec {source : Cloud (CrashModel.M Journal) Json} {tree target node}
    (expansion : Expansion source tree) (supported : PureProgram source)
    (route : TreeRoute tree Location.root target node)
    (initial : Durable) (valid : Valid tree initial) (activated : route.Activated initial.1)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Worker M)
    (worker : Worker) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    Triple (· = initial) ((step workerDb blobs fuel (journalMap.program source) target).run worker)
      (fun returned state => ∃ response, returned = (.ok response, worker) ∧
        Extends initial.1 state.1 ∧ Valid tree state ∧ state.2 = initial.2 ∧ tree.EmitsActivated state.1 response)
      (fun state => Extends initial.1 state.1 ∧ Valid tree state ∧ state.2 = initial.2) := by
  rw [step_eq blobs fuel source supported target worker]
  have sourceSpec := route.activated_step_spec expansion supported initial.1 valid.1 valid.2.1 activated
    comparable sameExit noBlobs fuel enough
  apply ((sourceSpec.withLeft (· = initial.2)).map (fun outcome => (outcome, worker))).weaken
  · intro state same; subst state; exact ⟨rfl, rfl⟩
  · intro returned state h
    obtain ⟨outcome, same, ⟨response, outcomeEq, progress, causal, emits⟩, untouched⟩ := h
    refine ⟨response, same.trans (congrArg (fun outcome => (outcome, worker)) outcomeEq), progress.1, ?_, untouched, emits⟩
    exact ⟨progress.2, causal, untouched ▸ valid.2.2.grow progress.1⟩
  · intro state h
    obtain ⟨⟨progress, causal⟩, untouched⟩ := h
    exact ⟨progress.1, ⟨progress.2, causal, untouched ▸ valid.2.2.grow progress.1⟩, untouched⟩

theorem report_eq {m : Type → Type} [Monad m] [LawfulMonad m] {σ : Type}
    (queue : WorkQueue σ m) (action : ExceptT CloudError (StateT σ m) StepResult)
    (location : Location) (worker : σ) :
    ((do
      let response ← action
      queue.complete location response
      pure response : ExceptT CloudError (StateT σ m) StepResult).run worker) =
      (do
        let (outcome, worker) ← action.run worker
        match outcome with
        | .error error => pure (.error error, worker)
        | .ok response => (fun returned => (.ok response, returned.2)) <$> queue.complete location response worker) := by
  change (action.run worker >>= _) = _
  congr 1
  funext (outcome, worker)
  cases outcome <;>
    simp [bind, ExceptT.bind, ExceptT.bindCont, StateT.bind,
      liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, StateT.pure, ExceptT.pure,
      pure, ← bind_pure_comp, bind_assoc]

end LeanCloud.Proofs.SharedRecovery
