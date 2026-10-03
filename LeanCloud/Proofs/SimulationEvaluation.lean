import LeanCloud.Proofs.EvaluationContinuation
import LeanCloud.Simulation
import LeanCloud.Proofs.PureBind

/-! The direct interpreter on pure programs issues no simulated operations.
Only reduction of pure binds is needed; the freer syntax is not assumed to
satisfy monad association as an equality of continuation queues. -/

namespace LeanCloud.Proofs
universe u
variable {m : Type → Type u} [Monad m] [PureBindLaw m]
open LeanEff DirectInterpreter.Internal

private theorem sim_pure_bind (value : α) (next : α → StateT σ m β) :
    (pure value >>= next) = next value := PureBindLaw.pure_bind value next

private theorem sim_map_pure (f : α → β) (value : α) :
    f <$> (pure value : StateT σ m α) = pure (f value) := by
  funext state
  change (pure (value, state) >>= _) = _
  rw [PureBindLaw.pure_bind]
  rfl

private theorem fold_pure (next : α → Fin count → α) (value : α) :
    Fin.foldlM (m := StateT σ m) count (fun value i => pure (next value i)) value =
      pure (Fin.foldlM (m := Id) count next value) := by
  induction count generalizing value with
  | zero => simp only [Fin.foldlM_zero]; rfl
  | succ count ih =>
    rw [Fin.foldlM_succ, Fin.foldlM_succ]
    simp only [sim_pure_bind]
    exact ih (fun value index => next value index.succ) (next value 0)

private theorem ofFnM_pure (values : Fin count → α) :
    (Array.ofFnM (fun index => pure (values index)) : StateT σ m (Array α)) =
      pure (Array.ofFn values) := by
  have original := Array.idRun_ofFnM (f := fun index => values index)
  unfold Array.ofFnM at original ⊢
  simp only [sim_map_pure]
  rw [fold_pure]
  exact congrArg Pure.pure original

mutual
  theorem Evaluation.simulation {program : Cloud m α} {outcome}
      (evaluation : Evaluation program outcome) (blobs : BlobStorage σ m) :
      (eval blobs program).run = pure outcome := by
    match evaluation with
    | .pure _ => rfl
    | .success head tail =>
      rw [eval, ExceptT.run_bind, head.simulation blobs]
      simpa only [sim_pure_bind] using tail.simulation blobs
    | .failure _ head =>
      rw [eval, ExceptT.run_bind, head.simulation blobs]
      simp only [sim_pure_bind]
  termination_by structural evaluation

  theorem ControlEvaluation.simulation {request : Control m α} {outcome}
      (evaluation : ControlEvaluation request outcome) (blobs : BlobStorage σ m) :
      (evalControl blobs request).run = pure outcome := by
    match evaluation with
    | .delay | .fail _ => rfl
    | .parallel (outcomes := outcomes) children =>
      obtain ⟨values, executed, collected⟩ := children.simulation blobs
      rw [evalControl, ExceptT.run_bind]
      change ((Except.ok <$> (Array.ofFnM fun index => (eval blobs _).run)) >>= _) = _
      rw [show (fun index => (eval blobs _).run) = (fun index => pure (values index)) from funext executed,
        ofFnM_pure, collected]
      simp only [sim_map_pure, sim_pure_bind]
      cases outcomes.mapM id <;> rfl
  termination_by structural evaluation

  theorem ContinuationEvaluation.simulation {continuation : ArrsF (Control m) α β}
      {value outcome} (evaluation : ContinuationEvaluation continuation value outcome)
      (blobs : BlobStorage σ m) :
      (evalContinuation blobs continuation value).run = pure outcome := by
    match evaluation with
    | .one program => exact program.simulation blobs
    | .success head tail =>
      rw [evalContinuation, ExceptT.run_bind, head.simulation blobs]
      simpa only [sim_pure_bind] using tail.simulation blobs
    | .failure _ head =>
      rw [evalContinuation, ExceptT.run_bind, head.simulation blobs]
      simp only [sim_pure_bind]
  termination_by structural evaluation

  theorem ChildrenEvaluation.simulation {count : Nat} {branches : Fin count → Cloud m α} {outcomes}
      (evaluation : ChildrenEvaluation branches outcomes) (blobs : BlobStorage σ m) :
      ∃ values : Fin count → Except CloudError α,
        (∀ index, (eval blobs (branches index)).run = pure (values index)) ∧ Array.ofFn values = outcomes := by
    match evaluation with
    | .empty _ => exact ⟨Fin.elim0, fun index => Fin.elim0 index, rfl⟩
    | .cons (outcome := outcome) head tail =>
      obtain ⟨values, executed, collected⟩ := tail.simulation blobs
      refine ⟨Fin.cases outcome values, ?_, ?_⟩
      · intro index
        cases index using Fin.cases with
        | zero => exact head.simulation blobs
        | succ index => exact executed index
      · simpa only [Array.ofFn_succ', Fin.cases_zero, Fin.cases_succ] using congrArg (#[outcome] ++ ·) collected
  termination_by structural evaluation
end

end LeanCloud.Proofs
