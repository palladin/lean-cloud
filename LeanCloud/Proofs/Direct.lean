import LeanCloud.DirectInterpreter

namespace LeanCloud.Proofs.Direct
open LeanEff DirectInterpreter.Internal

variable {m : Type → Type u} [Monad m] [LawfulMonad m] (blobs : BlobStorage m)

/-- Appending a continuation has ordinary monadic sequencing semantics. -/
theorem eval_bind (program : Cloud m α) (next : α → Cloud m β) :
    eval blobs (EffF.bind program next) =
      (eval blobs program >>= fun value => eval blobs (next value)) := by
  cases program <;> simp [EffF.bind, eval, evalContinuation, bind_assoc]

private theorem eval_viewLAppend (first : ArrsF (Control m) α β)
    (rest : ArrsF (Control m) β γ) (value : α) :
    (match first.viewLAppend rest with
      | .one next => eval blobs (next value)
      | .cons next tail => eval blobs (next value) >>= evalContinuation blobs tail) =
      (evalContinuation blobs first value >>= evalContinuation blobs rest) := by
  cases first with
  | one next => rfl
  | append first second =>
    simp only [ArrsF.viewLAppend]
    rw [eval_viewLAppend first (second.append rest) value]
    simp [evalContinuation, bind_assoc]
termination_by sizeOf first

private theorem eval_viewL (continuation : ArrsF (Control m) α β) (value : α) :
    (match continuation.viewL with
      | .one next => eval blobs (next value)
      | .cons next rest => eval blobs (next value) >>= evalContinuation blobs rest) =
      evalContinuation blobs continuation value := by
  cases continuation with
  | one next => rfl
  | append first rest => exact eval_viewLAppend blobs first rest value

/-- Replay applies a continuation queue; direct evaluation traverses it
structurally. Both operations have the same semantics. -/
theorem eval_apply (continuation : ArrsF (Control m) α β) (value : α) :
    eval blobs (continuation.apply value) = evalContinuation blobs continuation value := by
  rw [ArrsF.apply]
  split
  next next viewed => simpa [viewed] using eval_viewL blobs continuation value
  next next rest viewed =>
    rw [eval_bind]
    have tails : (fun value => eval blobs (rest.apply value)) = evalContinuation blobs rest := by
      funext value
      exact eval_apply rest value
    rw [tails]
    simpa [viewed] using eval_viewL blobs continuation value
termination_by sizeOf continuation
decreasing_by
  have smaller := ArrsF.viewL_rest_lt continuation
  simp_all

/-- The replay loop's flattened continuation preserves the direct meaning. -/
theorem eval_impure (control : Control m α) (continuation : ArrsF (Control m) α β) :
    eval blobs (.impure control continuation) =
      (evalControl blobs control >>= fun value => eval blobs (continuation.apply value)) := by
  simp only [eval, eval_apply]

end LeanCloud.Proofs.Direct
