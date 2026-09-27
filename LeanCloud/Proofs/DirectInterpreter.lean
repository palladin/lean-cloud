import LeanCloud.DirectInterpreter
import Init.Control.Lawful

/-! Composition laws for the existing direct interpreter. These apply to any
storage implementation over a lawful base monad; no codec assumptions are needed.
The continuation law connects structural evaluation with `ArrsF.apply`, which is
used by the replay interpreter to resume computations. -/

namespace LeanCloud.DirectInterpreter
open LeanEff Internal

variable {σ α β γ ι : Type} {m : Type → Type} [Monad m]

@[simp] theorem eval_pure (storage : Storage σ m) (value : α) :
    eval storage (EffF.pure value) = pure value := by
  rw [eval]

variable [LawfulMonad m]

/-- Interpreting a bind sequences the two interpretations, preserving effects,
state changes, and failure propagation in the target monad. -/
theorem eval_bind (storage : Storage σ m) (program : Cloud m α)
    (next : α → Cloud m β) :
    eval storage (EffF.bind program next) =
      (eval storage program >>= fun value => eval storage (next value)) := by
  cases program with
  | pure value => simp [EffF.bind, eval]
  | impure request continuation =>
    simp [EffF.bind, eval, evalContinuation, bind_assoc]

private theorem evalContinuation_viewLAppend {α β γ : Type} (storage : Storage σ m) :
    (first : ArrsF (Control m) α β) → (rest : ArrsF (Control m) β γ) → (value : α) →
    evalContinuation storage (.append first rest) value =
      match ArrsF.viewLAppend first rest with
      | .one k => eval storage (k value)
      | .cons k remaining =>
        eval storage (k value) >>= fun next => evalContinuation storage remaining next
  | .one _, _, _ => rfl
  | .append first second, rest, value => by
    simp only [ArrsF.viewLAppend]
    rw [← evalContinuation_viewLAppend storage first (.append second rest) value]
    simp only [evalContinuation, bind_assoc]
termination_by first => sizeOf first

private theorem evalContinuation_viewL (storage : Storage σ m)
    (continuation : ArrsF (Control m) α β) (value : α) :
    evalContinuation storage continuation value =
      match ArrsF.viewL continuation with
      | .one k => eval storage (k value)
      | .cons k rest =>
        eval storage (k value) >>= fun next => evalContinuation storage rest next := by
  cases continuation with
  | one k => rfl
  | append first rest =>
    have agrees := evalContinuation_viewLAppend storage first rest value
    cases view : ArrsF.viewLAppend first rest <;>
      simpa only [ArrsF.viewL, view] using agrees

/-- Applying a continuation queue and then interpreting it is equivalent to
interpreting the queue directly. This covers both left- and right-nested queues. -/
theorem eval_apply {α β : Type} (storage : Storage σ m)
    (continuation : ArrsF (Control m) α β) (value : α) :
    eval storage (ArrsF.apply continuation value) =
      evalContinuation storage continuation value := by
  rw [ArrsF.apply, evalContinuation_viewL]
  cases h : ArrsF.viewL continuation with
  | one k => rfl
  | cons k rest =>
    rw [eval_bind]
    congr 1
    funext next
    exact eval_apply storage rest next
termination_by sizeOf continuation
decreasing_by simpa [h] using ArrsF.viewL_rest_lt continuation

/-- Mapping the result commutes with interpretation, including encoding a branch
result for replay. -/
theorem eval_map (storage : Storage σ m) (f : α → β) (program : Cloud m α) :
    eval storage (f <$> program) = f <$> eval storage program := by
  change eval storage (EffF.bind program (fun value => .pure (f value))) = _
  rw [eval_bind]
  simp only [eval_pure, map_eq_pure_bind]

/-- The direct interpreter can be described with the same continuation operation
used by replay, without changing its structurally recursive implementation. -/
theorem eval_impure (storage : Storage σ m) (request : Control m α)
    (continuation : ArrsF (Control m) α β) :
    eval storage (.impure request continuation) =
      (evalControl storage request >>= fun value =>
        eval storage (ArrsF.apply continuation value)) := by
  simp only [eval, eval_apply]

theorem evalControl_empty_parallel (storage : Storage σ m) (codec : Codec α)
    (branches : Fin 0 → Cloud m α) :
    evalControl storage (.parallel codec 0 branches) = pure #[] := by
  rw [evalControl]
  simp only [Array.ofFnM_zero, liftM_pure, pure_bind, Array.mapM_empty]
  rfl

omit [LawfulMonad m] in
@[simp] theorem interpret_pure (storage : Storage σ m) (value : α) (input : ι) :
    interpret storage (fun _ : ι => pure value) input = pure value := by
  exact eval_pure storage value

theorem interpret_bind (storage : Storage σ m) (program : ι → Cloud m α)
    (next : α → Cloud m β) (input : ι) :
    interpret storage (fun input => program input >>= next) input =
      (interpret storage program input >>= fun value => interpret storage next value) := by
  exact eval_bind storage (program input) next

theorem interpret_map (storage : Storage σ m) (f : α → β)
    (program : ι → Cloud m α) (input : ι) :
    interpret storage (fun input => f <$> program input) input =
      f <$> interpret storage program input := by
  exact eval_map storage f (program input)

end LeanCloud.DirectInterpreter
