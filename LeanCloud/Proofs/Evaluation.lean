import LeanCloud.Proofs.Assumptions
import LeanCloud.DirectInterpreter
import LeanCloud.Proofs.Model

/-! Pure evaluation: values, delay, failure, and parallel. No external state or
primitive-effect histories participate in this relation. -/
universe u

namespace LeanCloud.Proofs
open LeanEff DirectInterpreter.Internal

mutual
  inductive Evaluation {m : Type → Type u} :
      {α : Type} → Cloud m α → Except CloudError α → Prop where
    | pure (value : α) : Evaluation (EffF.pure value) (.ok value)
    | success {request : Control m β} {continuation : ArrsF (Control m) β α}
        {value outcome}
        (head : ControlEvaluation request (.ok value))
        (tail : ContinuationEvaluation continuation value outcome) :
        Evaluation (.impure request continuation) outcome
    | failure {request : Control m β} (continuation : ArrsF (Control m) β α)
        {error} (head : ControlEvaluation request (.error error)) :
        Evaluation (.impure request continuation) (.error error)

  inductive ControlEvaluation {m : Type → Type u} :
      {α : Type} → Control m α → Except CloudError α → Prop where
    | delay : ControlEvaluation .delay (.ok ())
    | fail (error : CloudError) : ControlEvaluation (Control.fail (α := α) error) (.error error)
    | parallel {codec : Codec α} {count} {branches : Fin count → Cloud m α} {outcomes}
        (children : ChildrenEvaluation branches outcomes) :
        ControlEvaluation (.parallel codec count branches) (outcomes.mapM id)

  inductive ContinuationEvaluation {m : Type → Type u} : {α β : Type} →
      ArrsF (Control m) α β → α → Except CloudError β → Prop where
    | one {next : α → Cloud m β} {value outcome}
        (program : Evaluation (next value) outcome) :
        ContinuationEvaluation (.one next) value outcome
    | success {first : ArrsF (Control m) α β} {rest : ArrsF (Control m) β γ}
        {value next outcome}
        (head : ContinuationEvaluation first value (.ok next))
        (tail : ContinuationEvaluation rest next outcome) :
        ContinuationEvaluation (.append first rest) value outcome
    | failure {first : ArrsF (Control m) α β} (rest : ArrsF (Control m) β γ)
        {value error} (head : ContinuationEvaluation first value (.error error)) :
        ContinuationEvaluation (.append first rest) value (.error error)

  inductive ChildrenEvaluation {m : Type → Type u} : {α : Type} → {count : Nat} →
      (Fin count → Cloud m α) → Array (Except CloudError α) → Prop where
    | empty (branches : Fin 0 → Cloud m α) : ChildrenEvaluation branches #[]
    | cons {count : Nat} {branches : Fin (count + 1) → Cloud m α}
        {outcome outcomes}
        (head : Evaluation (branches 0) outcome)
        (tail : ChildrenEvaluation (fun index => branches index.succ) outcomes)
        :
        ChildrenEvaluation branches (#[outcome] ++ outcomes)
end

variable {m : Type → Type u}

/- Pure evaluation executes no operations in the underlying monad. This applies
also to the crash monad: the direct semantics has no crash boundaries or storage. -/
mutual
  theorem Evaluation.effect_free [Monad m] [LawfulMonad m] {program : Cloud m α} {outcome}
      (evaluation : Evaluation program outcome) (blobs : BlobStorage σ m) :
      (eval blobs program).run = pure outcome := by
    match evaluation with
    | .pure _ => rfl
    | .success head tail =>
      rw [eval, ExceptT.run_bind, head.effect_free blobs]
      simpa only [pure_bind] using tail.effect_free blobs
    | .failure _ head =>
      rw [eval, ExceptT.run_bind, head.effect_free blobs]
      simp only [pure_bind]
  termination_by structural evaluation

  theorem ControlEvaluation.effect_free [Monad m] [LawfulMonad m] {request : Control m α} {outcome}
      (evaluation : ControlEvaluation request outcome) (blobs : BlobStorage σ m) :
      (evalControl blobs request).run = pure outcome := by
    match evaluation with
    | .delay | .fail _ => rfl
    | .parallel (outcomes := outcomes) children =>
      rw [evalControl, ExceptT.run_bind]
      have executed := children.effect_free blobs
      change ((Except.ok <$> (Array.ofFnM fun index => (eval blobs _).run)) >>= _) = _
      rw [executed]
      simp only [map_pure, pure_bind]
      cases outcomes.mapM id <;> rfl
  termination_by structural evaluation

  theorem ContinuationEvaluation.effect_free [Monad m] [LawfulMonad m]
      {continuation : ArrsF (Control m) α β} {value outcome}
      (evaluation : ContinuationEvaluation continuation value outcome) (blobs : BlobStorage σ m) :
      (evalContinuation blobs continuation value).run = pure outcome := by
    match evaluation with
    | .one program => exact program.effect_free blobs
    | .success head tail =>
      rw [evalContinuation, ExceptT.run_bind, head.effect_free blobs]
      simpa only [pure_bind] using tail.effect_free blobs
    | .failure _ head =>
      rw [evalContinuation, ExceptT.run_bind, head.effect_free blobs]
      simp only [pure_bind]
  termination_by structural evaluation

  theorem ChildrenEvaluation.effect_free [Monad m] [LawfulMonad m]
      {count : Nat} {branches : Fin count → Cloud m α} {outcomes}
      (evaluation : ChildrenEvaluation branches outcomes) (blobs : BlobStorage σ m) :
      (Array.ofFnM fun index => (eval blobs (branches index)).run) = pure outcomes := by
    match evaluation with
    | .empty _ => simp [Array.ofFnM_zero]
    | .cons head tail =>
      rw [Array.ofFnM_succ', head.effect_free blobs]
      simp only [pure_bind]
      rw [tail.effect_free blobs]
      simp only [pure_bind]
  termination_by structural evaluation
end

/-- Specialization used by the ideal replay proof: the backend handle is unchanged. -/
theorem Evaluation.sound {program : Cloud Id α} {outcome}
    (evaluation : Evaluation program outcome) (blobs : BlobStorage σ Id) (state : σ) :
    (eval blobs program).run state = (outcome, state) := by rw [evaluation.effect_free blobs]; rfl

/-- Combine the finite evaluations of the children. -/
theorem ChildrenEvaluation.exists_of_children {count : Nat} (branches : Fin count → Cloud m α)
    (children : ∀ index, ∃ outcome, Evaluation (branches index) outcome) :
    ∃ outcomes, ChildrenEvaluation branches outcomes := by
  induction count with
  | zero => exact ⟨#[], .empty branches⟩
  | succ count ih =>
    obtain ⟨outcome, head⟩ := children 0
    obtain ⟨outcomes, tail⟩ := ih (fun index => branches index.succ) (fun index => children index.succ)
    exact ⟨_, .cons head tail⟩

mutual
  theorem Evaluation.exists (program : Cloud m α) (supported : PureProgram program) :
      ∃ outcome, Evaluation program outcome := by
    match program with
    | EffF.pure value => exact ⟨.ok value, .pure value⟩
    | .impure request continuation =>
      obtain ⟨outcome, head⟩ := ControlEvaluation.exists request supported.1
      cases outcome with
      | error error => exact ⟨_, .failure continuation head⟩
      | ok value =>
        obtain ⟨outcome, tail⟩ := ContinuationEvaluation.exists continuation supported.2 value
        exact ⟨outcome, .success head tail⟩
  termination_by structural program

  theorem ControlEvaluation.exists (request : Control m α) (supported : PureControl request) :
      ∃ outcome, ControlEvaluation request outcome := by
    match request with
    | .delay => exact ⟨_, .delay⟩
    | .fail error => exact ⟨_, .fail error⟩
    | .sequential .. | .choice .. => exact False.elim supported
    | .parallel _ _ branches =>
      obtain ⟨outcomes, children⟩ := ChildrenEvaluation.exists_of_children branches (fun index => Evaluation.exists (branches index) (supported.2 index))
      exact ⟨outcomes.mapM id, .parallel children⟩
  termination_by structural request

  theorem ContinuationEvaluation.exists (continuation : ArrsF (Control m) α β)
      (supported : PureContinuation continuation) (value : α) :
      ∃ outcome, ContinuationEvaluation continuation value outcome := by
    match continuation with
    | .one next =>
      obtain ⟨outcome, evaluation⟩ := Evaluation.exists (next value) (supported value)
      exact ⟨outcome, .one evaluation⟩
    | .append first rest =>
      obtain ⟨outcome, head⟩ := ContinuationEvaluation.exists first supported.1 value
      cases outcome with
      | error error => exact ⟨_, .failure rest head⟩
      | ok next =>
        obtain ⟨outcome, tail⟩ := ContinuationEvaluation.exists rest supported.2 next
        exact ⟨outcome, .success head tail⟩
  termination_by structural continuation

end

/-- A result of the existing direct interpreter, without a database or user world. -/
def direct (program : Cloud Id α) : Except CloudError α :=
  ((DirectInterpreter.interpret (noBlobs : BlobStorage Unit Id) (fun _ : Unit => program) ()).run ()).1

theorem Evaluation.result {program : Cloud Id α} {outcome} (evaluation : Evaluation program outcome) :
    direct program = outcome := congrArg Prod.fst (evaluation.sound noBlobs ())

/-- The direct interpreter of a pure workflow returns a fixed ordinary outcome
without calling the underlying monad or any blob backend. In particular, using
the crash monad introduces no crash boundary on the direct side. -/
theorem PureProgram.direct_effect_free [Monad m] [LawfulMonad m]
    (program : ι → Cloud m α) (input : ι) (supported : PureProgram (program input)) :
    ∃ outcome, Evaluation (program input) outcome ∧
      ∀ {σ : Type} (blobs : BlobStorage σ m),
        (DirectInterpreter.interpret blobs program input).run = pure outcome := by
  obtain ⟨outcome, evaluation⟩ := Evaluation.exists (program input) supported
  exact ⟨outcome, evaluation, fun _ => evaluation.effect_free _⟩

end LeanCloud.Proofs
