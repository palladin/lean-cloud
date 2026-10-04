import LeanCloud.Proofs.Direct

namespace LeanCloud.Proofs.Pure
open LeanEff DirectInterpreter.Internal

/-- A codec must preserve the values crossing a replay boundary. -/
def RoundTrips (codec : Codec α) : Prop :=
  ∀ value, codec.decode (codec.encode value) = .ok value

theorem RoundTrips.array (codec : Codec α) (roundtrip : RoundTrips codec) :
    RoundTrips (@instCodecArray α codec) := by
  intro values
  change (values.map codec.encode).mapM codec.decode = .ok values
  rw [Array.mapM_map]
  have same : (codec.decode ∘ codec.encode) = fun value => Except.ok value := funext roundtrip
  rw [same]
  change values.mapM (fun value => (pure value : Except String α)) = pure values
  simpa using (Array.mapM_pure (m := Except String) (xs := values) (f := id))

/-- Evidence for a pure Cloud computation, including delayed pure `exec`.
Parallel children may fail; their results are collected in source order.
Arbitrary base-monad actions and blob effects are deliberately outside this
relation. It describes existing Cloud programs, not another program type. -/
inductive Evaluation {m : Type → Type u} [Monad m] :
    {α : Type} → Cloud m α → Except CloudError α → Prop where
  | pure (value : α) : Evaluation (EffF.pure value) (.ok value)
  | fail (error : CloudError) (next : ArrsF (Control m) α β) :
      Evaluation (.impure (.fail error) next) (.error error)
  | delay (next : ArrsF (Control m) Unit α)
      (rest : Evaluation (next.apply ()) outcome) :
      Evaluation (.impure .delay next) outcome
  | exec (codec : Codec α) (label : String) (body : Unit → α)
      (next : ArrsF (Control m) α β)
      (roundtrip : codec.decode (codec.encode (body ())) = .ok (body ()))
      (rest : Evaluation (next.apply (body ())) outcome) :
      Evaluation (.impure (.command codec (.exec label (fun _ => pure (body ())))) next) outcome
  | parallelOk (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
      (next : ArrsF (Control m) (Array α) β) (outcomes : Fin count → Except CloudError α)
      (roundtrip : RoundTrips codec)
      (children : ∀ index, Evaluation (branches index) (outcomes index))
      (collected : (Array.ofFn outcomes).mapM id = .ok values)
      (rest : Evaluation (next.apply values) outcome) :
      Evaluation (.impure (.parallel codec count branches) next) outcome
  | parallelError (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
      (next : ArrsF (Control m) (Array α) β) (outcomes : Fin count → Except CloudError α)
      (roundtrip : RoundTrips codec)
      (children : ∀ index, Evaluation (branches index) (outcomes index))
      (collected : (Array.ofFn outcomes).mapM id = .error error) :
      Evaluation (.impure (.parallel codec count branches) next) (.error error)

private theorem eval_parallel {m : Type → Type u} [Monad m] [LawfulMonad m]
    (blobs : BlobStorage m) (codec : Codec α) (count : Nat) (branches : Fin count → Cloud m α)
    (outcomes : Fin count → Except CloudError α)
    (children : ∀ index, (eval blobs (branches index)).run = pure (outcomes index)) :
    (evalControl blobs (.parallel codec count branches)).run =
      pure ((Array.ofFn outcomes).mapM id) := by
  have same := funext children
  simp only [evalControl]
  rw [same, Array.ofFnM_pure]
  simp only [liftM_pure, pure_bind]
  cases (Array.ofFn outcomes).mapM id <;> rfl

/-- The actual direct interpreter returns the witnessed outcome without any
base-monad effects. In particular it does not read or modify an external world. -/
theorem evaluation_matches_direct {m : Type → Type u} [Monad m] [LawfulMonad m]
    (blobs : BlobStorage m) {program : Cloud m α} {outcome}
    (evaluation : Evaluation program outcome) :
    (eval blobs program).run = pure outcome := by
  induction evaluation with
  | pure value => rfl
  | fail error next => simp [eval, evalControl]
  | delay next rest ih =>
    rw [Direct.eval_impure]
    simpa [evalControl] using ih
  | exec codec label body next roundtrip rest ih =>
    rw [Direct.eval_impure]
    simpa [evalControl, BlobStorage.execute] using ih
  | parallelOk codec count branches next outcomes roundtrip children collected rest ihChildren ih =>
    rw [Direct.eval_impure]
    change (evalControl blobs (.parallel codec count branches)).run >>= _ = _
    rw [eval_parallel blobs codec count branches outcomes ihChildren, collected]
    simpa [ExceptT.bindCont, ExceptT.run] using ih
  | parallelError codec count branches next outcomes roundtrip children collected ihChildren =>
    rw [Direct.eval_impure]
    change (evalControl blobs (.parallel codec count branches)).run >>= _ = _
    rw [eval_parallel blobs codec count branches outcomes ihChildren, collected]
    simp [ExceptT.bindCont]

end LeanCloud.Proofs.Pure
