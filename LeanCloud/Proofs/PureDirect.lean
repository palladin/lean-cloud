import LeanCloud.Proofs.Pure
import LeanCloud.Proofs.ArrayEffects

/-! Pure direct evaluation also works when the base monad is lean-eff itself,
including SimM. Only computations that return without issuing a base effect
are compared; no syntactic associativity law is assumed for continuation queues. -/

namespace LeanCloud.Proofs.PureDirect
open LeanEff DirectInterpreter.Internal

variable {e : Type → Type u}

private theorem bind_returns (first : ExceptT ε (EffF e) α)
    (next : α → ExceptT ε (EffF e) β) (outcome : Except ε β) :
    (first >>= next).run = EffF.pure outcome ↔
      ∃ value, first.run = EffF.pure value ∧
        (match value with
         | .error error => outcome = .error error
         | .ok value => (next value).run = EffF.pure outcome) := by
  change EffF.bind first.run (ExceptT.bindCont next) = _ ↔ _
  cases found : first.run with
  | pure value =>
    cases value <;> simp [ExceptT.bindCont, EffF.bind, eq_comm]
    · change EffF.pure _ = EffF.pure outcome ↔ outcome = _
      simp [eq_comm]
    · rfl
  | impure request continuation =>
    simp [EffF.bind]

private theorem bind_returns_assoc (first : ExceptT ε (EffF e) α)
    (next : α → ExceptT ε (EffF e) β) (last : β → ExceptT ε (EffF e) γ)
    (outcome : Except ε γ) :
    ((first >>= next) >>= last).run = EffF.pure outcome ↔
      (first >>= fun value => next value >>= last).run = EffF.pure outcome := by
  change EffF.bind (EffF.bind first.run (ExceptT.bindCont next)) (ExceptT.bindCont last) = _ ↔
    EffF.bind first.run (ExceptT.bindCont (fun value => next value >>= last)) = _
  cases found : first.run with
  | pure value =>
    cases value <;> simp [ExceptT.bindCont, EffF.bind] <;> rfl
  | impure request continuation =>
    simp [EffF.bind]

variable (blobs : BlobStorage (EffF e))

private theorem eval_bind (program : Cloud (EffF e) α) (next : α → Cloud (EffF e) β)
    (outcome : Except CloudError β) :
    (eval blobs (EffF.bind program next)).run = EffF.pure outcome ↔
      (eval blobs program >>= fun value => eval blobs (next value)).run = EffF.pure outcome := by
  cases program with
  | pure value => rfl
  | impure request continuation =>
    exact (bind_returns_assoc (evalControl blobs request)
      (evalContinuation blobs continuation) (fun value => eval blobs (next value)) outcome).symm

private theorem eval_viewLAppend (first : ArrsF (Control (EffF e)) α β)
    (rest : ArrsF (Control (EffF e)) β γ) (value : α) (outcome : Except CloudError γ) :
    (match first.viewLAppend rest with
      | .one next => eval blobs (next value)
      | .cons next tail => eval blobs (next value) >>= evalContinuation blobs tail).run = EffF.pure outcome ↔
      (evalContinuation blobs first value >>= evalContinuation blobs rest).run = EffF.pure outcome := by
  cases first with
  | one next => rfl
  | append first second =>
    rw [ArrsF.viewLAppend, eval_viewLAppend first (second.append rest) value outcome]
    exact (bind_returns_assoc (evalContinuation blobs first value)
      (evalContinuation blobs second) (evalContinuation blobs rest) outcome).symm
termination_by sizeOf first

private theorem eval_viewL (next : ArrsF (Control (EffF e)) α β) (value : α)
    (outcome : Except CloudError β) :
    (match next.viewL with
      | .one next => eval blobs (next value)
      | .cons next rest => eval blobs (next value) >>= evalContinuation blobs rest).run = EffF.pure outcome ↔
      (evalContinuation blobs next value).run = EffF.pure outcome := by
  cases next with
  | one next => rfl
  | append first rest => exact eval_viewLAppend blobs first rest value outcome

private theorem eval_apply (next : ArrsF (Control (EffF e)) α β) (value : α)
    (outcome : Except CloudError β) :
    (eval blobs (next.apply value)).run = EffF.pure outcome ↔
      (evalContinuation blobs next value).run = EffF.pure outcome := by
  rw [ArrsF.apply]
  split
  next continuation viewed => simpa [viewed] using eval_viewL blobs next value outcome
  next continuation rest viewed =>
    rw [eval_bind]
    have same : (eval blobs (continuation value) >>= fun value => eval blobs (rest.apply value)).run = EffF.pure outcome ↔
        (eval blobs (continuation value) >>= evalContinuation blobs rest).run = EffF.pure outcome := by
      simp only [bind_returns]
      apply exists_congr
      intro result
      apply and_congr_right
      intro _
      cases result with
      | error _ => rfl
      | ok value => exact eval_apply rest value outcome
    exact same.trans (by simpa [viewed] using eval_viewL blobs next value outcome)
termination_by sizeOf next
decreasing_by
  have smaller := ArrsF.viewL_rest_lt next
  simp_all

private theorem ofFnM_pure (values : Fin count → α) :
    Array.ofFnM (fun index => EffF.pure (e := e) (values index)) = EffF.pure (Array.ofFn values) :=
  array_ofFnM_pure (m := EffF e) (fun _ _ => rfl) (fun _ _ => rfl) values

private theorem eval_parallel (codec : Codec α) (count : Nat) (branches : Fin count → Cloud (EffF e) α)
    (outcomes : Fin count → Except CloudError α)
    (children : ∀ index, (eval blobs (branches index)).run = EffF.pure (outcomes index)) :
    (evalControl blobs (.parallel codec count branches)).run =
      EffF.pure ((Array.ofFn outcomes).mapM id) := by
  simp only [evalControl]
  rw [funext children, ofFnM_pure]
  change (match (Array.ofFn outcomes).mapM id with
    | .ok values => EffF.pure (e := e) (Except.ok (ε := CloudError) values)
    | .error error => EffF.pure (Except.error error)) = _
  cases (Array.ofFn outcomes).mapM id <;> rfl

/-- The direct interpreter of a pure workflow is literally a pure base-monad
result. In SimM it therefore makes no atomic requests and changes no world. -/
theorem evaluation_matches_direct {program : Cloud (EffF e) α} {outcome}
    (evaluation : Pure.Evaluation program outcome) :
    (eval blobs program).run = EffF.pure outcome := by
  induction evaluation with
  | pure value => rfl
  | fail error next => rfl
  | delay next rest ih =>
    exact (eval_apply blobs next () _).mp ih
  | exec codec label body next roundtrip rest ih =>
    exact (eval_apply blobs next (body ()) _).mp ih
  | parallelOk codec count branches next outcomes roundtrip children collected rest ihChildren ih =>
    apply (bind_returns (evalControl blobs (.parallel codec count branches)) (evalContinuation blobs next) _).mpr
    exact ⟨.ok _, (eval_parallel blobs codec count branches outcomes ihChildren).trans (congrArg EffF.pure collected),
      (eval_apply blobs next _ _).mp ih⟩
  | parallelError codec count branches next outcomes roundtrip children collected ihChildren =>
    apply (bind_returns (evalControl blobs (.parallel codec count branches)) (evalContinuation blobs next) _).mpr
    exact ⟨.error _, (eval_parallel blobs codec count branches outcomes ihChildren).trans (congrArg EffF.pure collected), rfl⟩

end LeanCloud.Proofs.PureDirect
