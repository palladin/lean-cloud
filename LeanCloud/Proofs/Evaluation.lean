import LeanCloud.Proofs.Assumptions
import LeanCloud.DirectInterpreter
import LeanCloud.Proofs.Model

/-! Pure evaluation: values, delay, failure, and parallel. No external state or
primitive-effect histories participate in this relation. -/
namespace LeanCloud.Proofs
open LeanEff DirectInterpreter.Internal

mutual
  inductive Evaluation :
      {α : Type} → Cloud Id α → Except CloudError α → Prop where
    | pure (value : α) : Evaluation (EffF.pure value) (.ok value)
    | success {request : Control Id β} {continuation : ArrsF (Control Id) β α}
        {value outcome}
        (head : ControlEvaluation request (.ok value))
        (tail : ContinuationEvaluation continuation value outcome) :
        Evaluation (.impure request continuation) outcome
    | failure {request : Control Id β} (continuation : ArrsF (Control Id) β α)
        {error} (head : ControlEvaluation request (.error error)) :
        Evaluation (.impure request continuation) (.error error)

  inductive ControlEvaluation :
      {α : Type} → Control Id α → Except CloudError α → Prop where
    | delay : ControlEvaluation .delay (.ok ())
    | fail (error : CloudError) : ControlEvaluation (Control.fail (α := α) error) (.error error)
    | parallel {codec : Codec α} {count} {branches : Fin count → Cloud Id α} {outcomes}
        (children : ChildrenEvaluation branches outcomes) :
        ControlEvaluation (.parallel codec count branches) (outcomes.mapM id)

  inductive ContinuationEvaluation : {α β : Type} →
      ArrsF (Control Id) α β → α → Except CloudError β → Prop where
    | one {next : α → Cloud Id β} {value outcome}
        (program : Evaluation (next value) outcome) :
        ContinuationEvaluation (.one next) value outcome
    | success {first : ArrsF (Control Id) α β} {rest : ArrsF (Control Id) β γ}
        {value next outcome}
        (head : ContinuationEvaluation first value (.ok next))
        (tail : ContinuationEvaluation rest next outcome) :
        ContinuationEvaluation (.append first rest) value outcome
    | failure {first : ArrsF (Control Id) α β} (rest : ArrsF (Control Id) β γ)
        {value error} (head : ContinuationEvaluation first value (.error error)) :
        ContinuationEvaluation (.append first rest) value (.error error)

  inductive ChildrenEvaluation : {α : Type} → {count : Nat} →
      (Fin count → Cloud Id α) → Array (Except CloudError α) → Prop where
    | empty (branches : Fin 0 → Cloud Id α) : ChildrenEvaluation branches #[]
    | cons {count : Nat} {branches : Fin (count + 1) → Cloud Id α}
        {outcome outcomes}
        (head : Evaluation (branches 0) outcome)
        (tail : ChildrenEvaluation (fun index => branches index.succ) outcomes)
        :
        ChildrenEvaluation branches (#[outcome] ++ outcomes)
end

/- Pure evaluation agrees with the actual direct interpreter and preserves its
backend handle. No property of blob operations is needed: none is called. -/
mutual
  theorem Evaluation.sound {program : Cloud Id α} {outcome}
      (evaluation : Evaluation program outcome) (blobs : BlobStorage σ Id) (state : σ) :
      (eval blobs program).run state = (outcome, state) := by
    match evaluation with
    | .pure _ => rfl
    | .success head tail => rw [eval, run_bind_state, head.sound blobs state]; exact tail.sound blobs state
    | .failure _ head => rw [eval, run_bind_state, head.sound blobs state]
  termination_by structural evaluation

  theorem ControlEvaluation.sound {request : Control Id α} {outcome}
      (evaluation : ControlEvaluation request outcome) (blobs : BlobStorage σ Id) (state : σ) :
      (evalControl blobs request).run state = (outcome, state) := by
    match evaluation with
    | .delay | .fail _ => rfl
    | .parallel (branches := branches) (outcomes := outcomes) children =>
      rw [evalControl, run_bind_state]
      have executed := children.sound blobs state
      dsimp [liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk,
        ExceptT.run, Functor.map, StateT.map]
      dsimp only [ExceptT.run] at executed
      simp only [bind, pure, executed]
      cases outcomes.mapM id <;> rfl
  termination_by structural evaluation

  theorem ContinuationEvaluation.sound {continuation : ArrsF (Control Id) α β} {value outcome}
      (evaluation : ContinuationEvaluation continuation value outcome) (blobs : BlobStorage σ Id) (state : σ) :
      (evalContinuation blobs continuation value).run state = (outcome, state) := by
    match evaluation with
    | .one program => exact program.sound blobs state
    | .success head tail => rw [evalContinuation, run_bind_state, head.sound blobs state]; exact tail.sound blobs state
    | .failure _ head => rw [evalContinuation, run_bind_state, head.sound blobs state]
  termination_by structural evaluation

  theorem ChildrenEvaluation.sound {count : Nat} {branches : Fin count → Cloud Id α} {outcomes}
      (evaluation : ChildrenEvaluation branches outcomes) (blobs : BlobStorage σ Id) (state : σ) :
      (Array.ofFnM fun index => (eval blobs (branches index)).run) state = (outcomes, state) := by
    match evaluation with
    | .empty _ => simp [Array.ofFnM_zero]; rfl
    | .cons head tail =>
      rw [Array.ofFnM_succ']
      change (let (value, next) := (eval blobs (branches 0)).run state
        let (rest, last) := (Array.ofFnM fun index => (eval blobs (branches index.succ)).run) next
        (#[value] ++ rest, last)) = _
      rw [head.sound]
      dsimp only
      rw [tail.sound]
  termination_by structural evaluation
end

/-- Combine the finite evaluations of the children. -/
theorem ChildrenEvaluation.exists_of_children {count : Nat} (branches : Fin count → Cloud Id α)
    (children : ∀ index, ∃ outcome, Evaluation (branches index) outcome) :
    ∃ outcomes, ChildrenEvaluation branches outcomes := by
  induction count with
  | zero => exact ⟨#[], .empty branches⟩
  | succ count ih =>
    obtain ⟨outcome, head⟩ := children 0
    obtain ⟨outcomes, tail⟩ := ih (fun index => branches index.succ) (fun index => children index.succ)
    exact ⟨_, .cons head tail⟩

mutual
  theorem Evaluation.exists (program : Cloud Id α) (supported : PureProgram program) :
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

  theorem ControlEvaluation.exists (request : Control Id α) (supported : PureControl request) :
      ∃ outcome, ControlEvaluation request outcome := by
    match request with
    | .delay => exact ⟨_, .delay⟩
    | .fail error => exact ⟨_, .fail error⟩
    | .sequential .. | .choice .. => exact False.elim supported
    | .parallel _ _ branches =>
      obtain ⟨outcomes, children⟩ := ChildrenEvaluation.exists_of_children branches (fun index => Evaluation.exists (branches index) (supported.2 index))
      exact ⟨outcomes.mapM id, .parallel children⟩
  termination_by structural request

  theorem ContinuationEvaluation.exists (continuation : ArrsF (Control Id) α β)
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

end LeanCloud.Proofs
