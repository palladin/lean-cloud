import LeanCloud.Proofs.BackendFootprint

namespace LeanCloud.Backend.Proofs
open Lean LeanEff LeanCloud.Proofs

def replayView (action : Replay.M α) : Program (Except String α) := Program.ofEff action.run

theorem replayView_pure (value : α) : replayView (pure value) = .pure (.ok value) := rfl

theorem replayView_bind (action : Replay.M α) (next : α → Replay.M β) :
    replayView (action >>= next) = (replayView action).bind (fun result =>
      match result with
      | .error error => .pure (.error error)
      | .ok value => replayView (next value)) := by
  unfold replayView
  change Program.ofEff (action.run >>= ExceptT.bindCont next) = _
  rw [Program.ofEff_bind]
  congr 1
  funext result
  cases result <;> rfl

/-- The leased adapter preserves every request and carries its receipt through
the same continuation. Infrastructure errors remain outside Cloud errors. -/
def WithHandle (source : ExceptT ε (StateT σ Replay.M) α)
    (target : ExceptT ε (StateT (LeaseQueue.Worker σ ρ) Replay.M) α) : Prop :=
  ∀ worker, replayView (LeaseQueue.liftBackend source.run worker) = replayView (target.run worker)

namespace WithHandle

theorem pure (value : α) : WithHandle (pure value : ExceptT ε (StateT σ Replay.M) α)
    (pure value : ExceptT ε (StateT (LeaseQueue.Worker σ ρ) Replay.M) α) := by
  intro worker
  rfl

theorem throw (error : ε) : WithHandle (throw error : ExceptT ε (StateT σ Replay.M) α)
    (throw error : ExceptT ε (StateT (LeaseQueue.Worker σ ρ) Replay.M) α) := by
  intro worker
  rfl

theorem lift (action : StateT σ Replay.M α) :
    WithHandle (liftM action : ExceptT ε (StateT σ Replay.M) α)
      (liftM (LeaseQueue.liftBackend (ρ := ρ) action) :
        ExceptT ε (StateT (LeaseQueue.Worker σ ρ) Replay.M) α) := by
  intro worker
  change replayView ((action worker.backend >>= fun pair => Pure.pure ((Except.ok pair.1 : Except ε α), pair.2)) >>=
    fun pair => Pure.pure (pair.1, { worker with backend := pair.2 })) =
    replayView ((action worker.backend >>= fun pair => Pure.pure (pair.1, { worker with backend := pair.2 })) >>=
      fun pair => Pure.pure ((Except.ok pair.1 : Except ε α), pair.2))
  simp only [replayView_bind, Program.bind_assoc, replayView_pure]
  congr 1
  funext result
  cases result <;> rfl

theorem bind {source : ExceptT ε (StateT σ Replay.M) α}
    {target : ExceptT ε (StateT (LeaseQueue.Worker σ ρ) Replay.M) α}
    (same : WithHandle source target)
    {left : α → ExceptT ε (StateT σ Replay.M) β}
    {right : α → ExceptT ε (StateT (LeaseQueue.Worker σ ρ) Replay.M) β}
    (next : ∀ value, WithHandle (left value) (right value)) :
    WithHandle (source >>= left) (target >>= right) := by
  intro worker
  change replayView ((source.run worker.backend >>= fun pair =>
    ExceptT.bindCont left pair.1 pair.2) >>= fun pair =>
      Pure.pure (pair.1, { worker with backend := pair.2 })) =
    replayView (target.run worker >>= fun pair =>
      ExceptT.bindCont right pair.1 pair.2)
  simp only [replayView_bind]
  rw [← same worker]
  simp only [LeaseQueue.liftBackend, replayView_bind, Program.bind_assoc, replayView_pure]
  congr 1
  funext result
  cases result with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨outcome, backend⟩
    cases outcome with
    | error error => rfl
    | ok value =>
      simpa only [WithHandle, LeaseQueue.liftBackend, replayView_bind, replayView_pure,
        Program.bind, ExceptT.bindCont, ExceptT.run] using next value { worker with backend }

end WithHandle

private def relation (db : Db σ Replay.M) : ReplayRelation db (LeaseQueue.db (ρ := ρ) db) where
  relates := WithHandle
  pure := WithHandle.pure
  throw := WithHandle.throw
  bind := WithHandle.bind
  get key := WithHandle.lift (db.get key)
  put key value := WithHandle.lift (db.put key value)

theorem leased_step (db : Db σ Replay.M) (blobs : BlobStorage σ Replay.M)
    (leasedBlobs : BlobStorage (LeaseQueue.Worker σ ρ) Replay.M) (fuel : Nat)
    (program : Cloud Replay.M Json) (supported : PureProgram program) (location : Location) :
    WithHandle (ReplayInterpreter.Internal.step db blobs fuel program location)
      (ReplayInterpreter.Internal.step (LeaseQueue.db db) leasedBlobs fuel program location) :=
  (relation db).step blobs leasedBlobs fuel program supported location

namespace Journal

theorem ActionChecked.leased {expected : View}
    {action : Action α}
    {leased : ExceptT CloudError (StateT Replay.Worker Replay.M) α}
    {post : α → Backend.State → Prop} {state : Backend.State}
    (safe : ActionChecked expected action post state) (valid : Valid expected state)
    (stable : ∀ value before after, Grows before after → post value before → post value after)
    (same : WithHandle action leased) (worker : Replay.Worker) :
    ProgramSafe (Valid expected) Grows
      (fun returned final => ∃ value, returned = .ok (.ok value, worker) ∧ post value final)
      ((leased.run worker).run) state := by
  change Safe _ _ _ (replayView (leased.run worker)) _
  rw [← same worker]
  unfold LeaseQueue.liftBackend
  rw [replayView_bind]
  cases worker with
  | mk backend delivery =>
    cases backend
    apply Safe.bind Grows.refl (fun a b => a.trans b) safe valid
    intro returned current kept growth done
    obtain ⟨result, rfl, value, rfl, result⟩ := done
    exact .pure fun final bounded later => ⟨value, rfl, stable value current final later result⟩

theorem Emits.grow {tree response before after} (emitted : Emits tree response before)
    (growth : Grows before after) : Emits tree response after := by
  cases response with
  | done outcome => exact emitted
  | runnable locations => exact fun location member => (emitted location member).grow growth

theorem leased_step_checked {program : Cloud Replay.M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : (node.exit == node.exit) = true)
    (state : Backend.State) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel)
    (worker : Replay.Worker) :
    ProgramSafe (Valid (tree.journal Location.root)) Grows
      (fun returned final => ∃ response, returned = .ok (.ok response, worker) ∧ Emits tree response final ∧
        StepProgress tree current node state response final)
      (((ReplayInterpreter.Internal.step Replay.db Replay.noBlobs fuel program current).run worker).run) state := by
  let blobs : BlobStorage Unit Replay.M := {
    putBlob := fun _ => throw ⟨.unsupported, "Unused in pure programs"⟩
    readBlob := fun _ => throw ⟨.unsupported, "Unused in pure programs"⟩
    resolveBlob := fun _ => throw ⟨.unsupported, "Unused in pure programs"⟩ }
  exact (step_progress whole supported route comparable sameExit blobs state valid active fuel enough).leased valid
    (fun _ _ _ growth h => ⟨h.1.grow growth, h.2.grow (.refl _) growth⟩)
    (leased_step workerDb blobs Replay.noBlobs fuel program supported current) worker

end Journal

end LeanCloud.Backend.Proofs
