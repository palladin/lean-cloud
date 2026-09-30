import LeanCloud.Proofs.Evaluation

/-! Processing work in a completed evaluation. Delays are transparent to the
queue; a parallel group needs a fork and a join. Successful branch returns need
one final report, while failures report during their failing command.

The delay cost is zero for queue progress and one for reconstruction
termination. Both measures use the same evaluation and continuation laws. -/

universe u

namespace LeanCloud.Proofs
open LeanEff

def returnWork : Except CloudError α → Nat
  | .ok _ => 1
  | .error _ => 0

mutual
  inductive ProgramWork {m : Type → Type u} (delayCost : Nat) : {α : Type} → {program : Cloud m α} →
      {outcome : Except CloudError α} → Evaluation program outcome → Nat → Prop where
    | pure (value : α) : ProgramWork delayCost (Evaluation.pure value) 0
    | success {request : Control m β} {continuation : ArrsF (Control m) β α}
        {value outcome controlWork restWork}
        {head : ControlEvaluation request (.ok value)} {tail : ContinuationEvaluation continuation value outcome}
        (control : ControlWork delayCost head controlWork) (remaining : ContinuationWork delayCost tail restWork) :
        ProgramWork delayCost (.success head tail) (controlWork + restWork)
    | failure {request : Control m β} (continuation : ArrsF (Control m) β α)
        {error work} {head : ControlEvaluation request (.error error)}
        (control : ControlWork delayCost head work) : ProgramWork delayCost (.failure continuation head) work

  inductive ControlWork {m : Type → Type u} (delayCost : Nat) : {α : Type} → {request : Control m α} →
      {outcome : Except CloudError α} → ControlEvaluation request outcome → Nat → Prop where
    | delay : ControlWork delayCost (ControlEvaluation.delay) delayCost
    | fail (error : CloudError) : ControlWork delayCost (ControlEvaluation.fail (α := α) error) 1
    | parallel {codec : Codec α} {count : Nat} {branches : Fin count → Cloud m α}
        {outcomes work} {children : ChildrenEvaluation branches outcomes}
        (cost : ChildrenWork delayCost children work) : ControlWork delayCost (.parallel (codec := codec) children) (work + 2)

  inductive ContinuationWork {m : Type → Type u} (delayCost : Nat) : {α β : Type} → {continuation : ArrsF (Control m) α β} →
      {value : α} → {outcome : Except CloudError β} →
        ContinuationEvaluation continuation value outcome → Nat → Prop where
    | one {k : α → Cloud m β} {value outcome work} {evaluation : Evaluation (k value) outcome}
        (cost : ProgramWork delayCost evaluation work) : ContinuationWork delayCost (.one evaluation) work
    | success {first : ArrsF (Control m) α β} {rest : ArrsF (Control m) β γ}
        {value next outcome firstWork restWork}
        {head : ContinuationEvaluation first value (.ok next)} {tail : ContinuationEvaluation rest next outcome}
        (first : ContinuationWork delayCost head firstWork) (rest : ContinuationWork delayCost tail restWork) :
        ContinuationWork delayCost (.success head tail) (firstWork + restWork)
    | failure {first : ArrsF (Control m) α β} (rest : ArrsF (Control m) β γ)
        {value error work} {head : ContinuationEvaluation first value (.error error)}
        (cost : ContinuationWork delayCost head work) : ContinuationWork delayCost (.failure rest head) work

  inductive ChildrenWork {m : Type → Type u} (delayCost : Nat) : {α : Type} → {count : Nat} → {branches : Fin count → Cloud m α} →
      {outcomes : Array (Except CloudError α)} →
        ChildrenEvaluation branches outcomes → Nat → Prop where
    | empty (branches : Fin 0 → Cloud m α) : ChildrenWork delayCost (.empty branches) 0
    | cons {count : Nat} {branches : Fin (count + 1) → Cloud m α}
        {outcome outcomes firstWork restWork}
        {head : Evaluation (branches 0) outcome}
        {tail : ChildrenEvaluation (fun index => branches index.succ) outcomes}
        (first : ProgramWork delayCost head firstWork) (rest : ChildrenWork delayCost tail restWork)
        :
        ChildrenWork delayCost (.cons head tail) (firstWork + returnWork outcome + restWork)
end

variable {m : Type → Type u} {delayCost : Nat}

mutual
  theorem Evaluation.work_exists {program : Cloud m α} {outcome}
      (evaluation : Evaluation program outcome) (delayCost : Nat := 0) : ∃ work, ProgramWork delayCost evaluation work := by
    match evaluation with
    | .pure value => exact ⟨0, .pure value⟩
    | .success head tail =>
      obtain ⟨first, headWork⟩ := head.work_exists delayCost
      obtain ⟨rest, tailWork⟩ := tail.work_exists delayCost
      exact ⟨first + rest, .success headWork tailWork⟩
    | .failure continuation head =>
      obtain ⟨work, cost⟩ := head.work_exists delayCost
      exact ⟨work, .failure continuation cost⟩
  termination_by structural evaluation

  theorem ControlEvaluation.work_exists {request : Control m α} {outcome}
      (evaluation : ControlEvaluation request outcome) (delayCost : Nat := 0) : ∃ work, ControlWork delayCost evaluation work := by
    match evaluation with
    | .delay => exact ⟨delayCost, .delay⟩
    | .fail error => exact ⟨1, .fail error⟩
    | .parallel children =>
      obtain ⟨work, cost⟩ := children.work_exists delayCost
      exact ⟨work + 2, .parallel cost⟩
  termination_by structural evaluation

  theorem ContinuationEvaluation.work_exists {continuation : ArrsF (Control m) α β}
      {value outcome} (evaluation : ContinuationEvaluation continuation value outcome) (delayCost : Nat := 0) :
      ∃ work, ContinuationWork delayCost evaluation work := by
    match evaluation with
    | .one program =>
      obtain ⟨work, cost⟩ := program.work_exists delayCost
      exact ⟨work, .one cost⟩
    | .success head tail =>
      obtain ⟨first, headWork⟩ := head.work_exists delayCost
      obtain ⟨rest, tailWork⟩ := tail.work_exists delayCost
      exact ⟨first + rest, .success headWork tailWork⟩
    | .failure rest head =>
      obtain ⟨work, cost⟩ := head.work_exists delayCost
      exact ⟨work, .failure rest cost⟩
  termination_by structural evaluation

  theorem ChildrenEvaluation.work_exists {count : Nat} {branches : Fin count → Cloud m α}
      {outcomes} (evaluation : ChildrenEvaluation branches outcomes) (delayCost : Nat := 0) : ∃ work, ChildrenWork delayCost evaluation work := by
    match evaluation with
    | .empty branches => exact ⟨0, .empty branches⟩
    | .cons head tail =>
      obtain ⟨first, headWork⟩ := head.work_exists delayCost
      obtain ⟨rest, tailWork⟩ := tail.work_exists delayCost
      exact ⟨_, .cons headWork tailWork⟩
  termination_by structural evaluation
end

mutual
  theorem ProgramWork.total_positive {α : Type} {program : Cloud m α}
      {outcome work} {evaluation : Evaluation program outcome} (cost : ProgramWork delayCost evaluation work) :
      0 < work + returnWork outcome := by
    match cost with
    | .pure _ => simp [returnWork]
    | .success head tail => have := tail.total_positive; omega
    | .failure continuation head => exact head.total_positive
  termination_by structural cost

  theorem ControlWork.total_positive {α : Type} {request : Control m α}
      {outcome work} {evaluation : ControlEvaluation request outcome} (cost : ControlWork delayCost evaluation work) :
      0 < work + returnWork outcome := by
    match cost with
    | .delay => simp [returnWork]
    | .fail _ => simp [returnWork]
    | .parallel .. => omega

  theorem ContinuationWork.total_positive {α β : Type} {continuation : ArrsF (Control m) α β}
      {value outcome work} {evaluation : ContinuationEvaluation continuation value outcome}
      (cost : ContinuationWork delayCost evaluation work) : 0 < work + returnWork outcome := by
    match cost with
    | .one head => exact head.total_positive
    | .success head tail => have := tail.total_positive; omega
    | .failure rest head => exact head.total_positive
  termination_by structural cost
end

theorem ControlWork.positive {request : Control m α} {outcome work}
    {evaluation : ControlEvaluation request outcome} (cost : ControlWork 1 evaluation work) :
    0 < work := by
  cases cost <;> omega

/-- Retyping the collected result preserves a group's work count. -/
theorem ChildrenWork.control {α : Type} (codec : Codec α) {count : Nat}
    {branches : Fin count → Cloud m α} {outcomes work outcome}
    {evaluation : ChildrenEvaluation branches outcomes} (cost : ChildrenWork delayCost evaluation work)
    (collected : outcomes.mapM id = outcome) :
    ∃ head : ControlEvaluation (.parallel codec count branches) outcome, ControlWork delayCost head (work + 2) := by
  subst outcome
  exact ⟨_, .parallel cost⟩

private theorem ControlWork.shape {request : Control m α} {outcome work}
    {evaluation : ControlEvaluation request outcome} (cost : ControlWork delayCost evaluation work) :
    match request with
    | .delay => outcome = .ok () ∧ work = delayCost
    | .fail error => outcome = .error error ∧ work = 1
    | .parallel _ _ branches => ∃ outcomes childWork, ∃ children : ChildrenEvaluation branches outcomes,
        ChildrenWork delayCost children childWork ∧ outcome = outcomes.mapM id ∧ work = childWork + 2
    | .sequential .. | .choice .. => False := by
  cases cost with
  | delay => exact ⟨rfl, rfl⟩
  | fail => exact ⟨rfl, rfl⟩
  | parallel children => exact ⟨_, _, _, children, rfl, rfl⟩

/- The amount of pure work is determined by the program, independently of
which parallel child the queue selects first. -/
mutual
  theorem ProgramWork.unique {program : Cloud m α} {outcome work}
      {evaluation : Evaluation program outcome} (cost : ProgramWork delayCost evaluation work) :
      ∀ {otherOutcome otherWork} {other : Evaluation program otherOutcome},
      ProgramWork delayCost other otherWork → outcome = otherOutcome ∧ work = otherWork := by
    intro otherOutcome otherWork other otherCost
    match cost with
    | .pure value => cases otherCost; exact ⟨rfl, rfl⟩
    | .success head tail =>
      cases otherCost with
      | success otherHead otherTail =>
        obtain ⟨same, headWork⟩ := head.unique otherHead
        cases same
        obtain ⟨result, tailWork⟩ := tail.unique otherTail
        exact ⟨result, by omega⟩
      | failure _ otherHead => cases (head.unique otherHead).1
    | .failure _ head =>
      cases otherCost with
      | success otherHead _ => cases (head.unique otherHead).1
      | failure _ otherHead =>
        obtain ⟨same, work⟩ := head.unique otherHead
        exact ⟨congrArg Except.error (Except.error.inj same), work⟩
  termination_by structural cost

  theorem ControlWork.unique {request : Control m α} {outcome work}
      {evaluation : ControlEvaluation request outcome} (cost : ControlWork delayCost evaluation work) :
      ∀ {otherOutcome otherWork} {other : ControlEvaluation request otherOutcome},
      ControlWork delayCost other otherWork → outcome = otherOutcome ∧ work = otherWork := by
    match α, request, outcome, work, evaluation, cost with
    | _, _, _, _, _, .delay =>
      intro otherOutcome otherWork other otherCost
      exact ⟨otherCost.shape.1.symm, otherCost.shape.2.symm⟩
    | _, _, _, _, _, .fail error =>
      intro otherOutcome otherWork other otherCost
      exact ⟨otherCost.shape.1.symm, otherCost.shape.2.symm⟩
    | _, _, _, _, _, .parallel children =>
      intro otherOutcome otherWork other otherCost
      obtain ⟨outcomes, childWork, evaluation, otherChildren, sameOutcome, sameWork⟩ := otherCost.shape
      obtain ⟨same, childWorkEq⟩ := children.unique otherChildren
      exact ⟨(congrArg (fun outcomes => outcomes.mapM id) same).trans sameOutcome.symm, by omega⟩
  termination_by structural cost

  theorem ContinuationWork.unique {continuation : ArrsF (Control m) α β} {value outcome work}
      {evaluation : ContinuationEvaluation continuation value outcome} (cost : ContinuationWork delayCost evaluation work) :
      ∀ {otherOutcome otherWork} {other : ContinuationEvaluation continuation value otherOutcome},
      ContinuationWork delayCost other otherWork → outcome = otherOutcome ∧ work = otherWork := by
    intro otherOutcome otherWork other otherCost
    match cost with
    | .one head => cases otherCost with | one otherHead => exact head.unique otherHead
    | .success head tail =>
      cases otherCost with
      | success otherHead otherTail =>
        obtain ⟨same, headWork⟩ := head.unique otherHead
        cases same
        obtain ⟨result, tailWork⟩ := tail.unique otherTail
        exact ⟨result, by omega⟩
      | failure _ otherHead => cases (head.unique otherHead).1
    | .failure _ head =>
      cases otherCost with
      | success otherHead _ => cases (head.unique otherHead).1
      | failure _ otherHead =>
        obtain ⟨same, work⟩ := head.unique otherHead
        exact ⟨congrArg Except.error (Except.error.inj same), work⟩
  termination_by structural cost

  theorem ChildrenWork.unique {count : Nat} {branches : Fin count → Cloud m α} {outcomes work}
      {evaluation : ChildrenEvaluation branches outcomes} (cost : ChildrenWork delayCost evaluation work) :
      ∀ {otherOutcomes otherWork} {other : ChildrenEvaluation branches otherOutcomes},
      ChildrenWork delayCost other otherWork → outcomes = otherOutcomes ∧ work = otherWork := by
    intro otherOutcomes otherWork other otherCost
    match cost with
    | .empty .. => cases otherCost; exact ⟨rfl, rfl⟩
    | .cons head tail =>
      cases otherCost with
      | cons otherHead otherTail =>
        obtain ⟨same, headWork⟩ := head.unique otherHead
        subst same
        obtain ⟨sameResults, tailWork⟩ := tail.unique otherTail
        exact ⟨by rw [sameResults], by omega⟩
  termination_by structural cost
end

/-- The pure result is determined by the program, without assumptions on the
underlying monad or its external actions. -/
theorem Evaluation.unique {program : Cloud m α} {left right : Except CloudError α}
    (first : Evaluation program left) (second : Evaluation program right) : left = right := by
  obtain ⟨_, a⟩ := first.work_exists
  obtain ⟨_, b⟩ := second.work_exists
  exact (a.unique b).1

theorem ChildrenEvaluation.unique {count : Nat} {branches : Fin count → Cloud m α} {left right}
    (first : ChildrenEvaluation branches left) (second : ChildrenEvaluation branches right) : left = right := by
  obtain ⟨_, a⟩ := first.work_exists
  obtain ⟨_, b⟩ := second.work_exists
  exact (a.unique b).1

end LeanCloud.Proofs
