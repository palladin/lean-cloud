import LeanCloud.Proofs.EvaluationWork
import LeanCloud.Proofs.Codecs
import LeanCloud.Proofs.PureContinuation

/-! Rebuilding continuations and encoding branch results do not add processing
work. Intermediate pure values in a bind are not worker completion reports. -/

namespace LeanCloud.Proofs
open LeanEff

variable {m : Type → Type} {delayCost : Nat}

theorem ChildrenEvaluation.size {α : Type} {count : Nat}
    {branches : Fin count → Cloud m α} {outcomes}
    (evaluation : ChildrenEvaluation branches outcomes) : outcomes.size = count := by
  match evaluation with
  | .empty _ => rfl
  | .cons _ tail => simp [tail.size, Nat.add_comm]
termination_by structural evaluation

theorem ProgramWork.bind_cases {α β : Type}
    (program : Cloud m α) (next : α → Cloud m β)
    {outcome : Except CloudError β} {work}
    {evaluation : Evaluation (EffF.bind program next) outcome}
    (cost : ProgramWork delayCost evaluation work) :
    (∃ value firstWork restWork, ∃ (head : Evaluation program (.ok value))
      (tail : Evaluation (next value) outcome),
      ProgramWork delayCost head firstWork ∧ ProgramWork delayCost tail restWork ∧
      work = firstWork + restWork) ∨
    (∃ error, ∃ (head : Evaluation program (.error error)),
      ProgramWork delayCost head work ∧ outcome = .error error) := by
  cases program with
  | pure value => exact .inl ⟨value, 0, work, .pure value, evaluation, .pure value, cost, by omega⟩
  | impure request continuation =>
    cases cost with
    | success head tail =>
      cases tail with
      | success first rest =>
        cases rest with
        | one last => exact .inl ⟨_, _, _, _, _, .success head first, last, by omega⟩
      | failure _ first => exact .inr ⟨_, _, .success head first, rfl⟩
    | failure _ head => exact .inr ⟨_, _, .failure continuation head, rfl⟩

theorem ProgramWork.map_cases {α β : Type} (program : Cloud m α)
    (f : α → β) {outcome : Except CloudError β} {work}
    {evaluation : Evaluation (f <$> program) outcome} (cost : ProgramWork delayCost evaluation work) :
    ∃ original, ∃ (head : Evaluation program original),
      ProgramWork delayCost head work ∧ outcome = original.map f := by
  rcases cost.bind_cases program (fun value => EffF.pure (f value)) with success | failure
  · obtain ⟨value, firstWork, restWork, head, tail, headCost, tailCost, workEq⟩ := success
    cases tailCost
    simp only [Nat.add_zero] at workEq
    subst work
    exact ⟨.ok value, head, headCost, rfl⟩
  · obtain ⟨error, head, headCost, rfl⟩ := failure
    exact ⟨.error error, head, headCost, rfl⟩

theorem Evaluation.map_cases {α β : Type} (program : Cloud m α)
    (f : α → β) {outcome : Except CloudError β}
    (evaluation : Evaluation (f <$> program) outcome) :
    ∃ original, Evaluation program original ∧ outcome = original.map f := by
  obtain ⟨_, cost⟩ := evaluation.work_exists
  obtain ⟨original, head, _, same⟩ := cost.map_cases program f
  exact ⟨original, head, same⟩

theorem ProgramWork.of_encoded {α : Type} (codec : Codec α) (law : CodecLaw codec)
    (program : Cloud m α) {outcome : Except CloudError α} {work}
    {evaluation : Evaluation (codec.encode <$> program) (outcome.map codec.encode)}
    (cost : ProgramWork delayCost evaluation work) :
    ∃ result : Evaluation program outcome, ProgramWork delayCost result work := by
  obtain ⟨original, originalEvaluation, originalCost, equal⟩ := cost.map_cases program codec.encode
  cases original with
  | error error =>
    cases outcome with
    | ok _ => cases equal
    | error other => cases equal; exact ⟨_, originalCost⟩
  | ok value =>
    cases outcome with
    | error _ => cases equal
    | ok other =>
      have same := codec_encode_injective codec law (Except.ok.inj equal)
      subst other
      exact ⟨_, originalCost⟩

private theorem ContinuationWork.associate_left {α β γ δ : Type}
    {first : ArrsF (Control m) α β} {second : ArrsF (Control m) β γ}
    {rest : ArrsF (Control m) γ δ} {value : α}
    {outcome : Except CloudError δ} {work}
    {evaluation : ContinuationEvaluation (.append first (.append second rest)) value outcome}
    (cost : ContinuationWork delayCost evaluation work) :
    ∃ result : ContinuationEvaluation (.append (.append first second) rest) value outcome,
      ContinuationWork delayCost result work := by
  cases cost with
  | success head tail =>
    cases tail with
    | success middle last =>
      have shifted := ContinuationWork.success (.success head middle) last
      simp only [Nat.add_assoc] at shifted
      exact ⟨_, shifted⟩
    | failure _ middle => exact ⟨_, .failure rest (.success head middle)⟩
  | failure _ head => exact ⟨_, .failure rest (.failure second head)⟩

private theorem ContinuationWork.of_viewLAppend {α β γ : Type}
    (first : ArrsF (Control m) α β) (rest : ArrsF (Control m) β γ)
    (value : α) {outcome : Except CloudError γ} {work}
    (cost : match ArrsF.viewLAppend first rest with
      | .one k => ∃ evaluation : Evaluation (k value) outcome, ProgramWork delayCost evaluation work
      | .cons k remaining => ∃ evaluation : ContinuationEvaluation (.append (.one k) remaining) value outcome,
          ContinuationWork delayCost evaluation work) :
    ∃ evaluation : ContinuationEvaluation (.append first rest) value outcome, ContinuationWork delayCost evaluation work := by
  match first with
  | .one k => exact cost
  | .append first second =>
    obtain ⟨_, shifted⟩ := ContinuationWork.of_viewLAppend first (.append second rest) value cost
    exact shifted.associate_left
termination_by sizeOf first

private theorem ContinuationWork.of_viewL {α β : Type}
    (continuation : ArrsF (Control m) α β) (value : α)
    {outcome : Except CloudError β} {work}
    (cost : match ArrsF.viewL continuation with
      | .one k => ∃ evaluation : Evaluation (k value) outcome, ProgramWork delayCost evaluation work
      | .cons k remaining => ∃ evaluation : ContinuationEvaluation (.append (.one k) remaining) value outcome,
          ContinuationWork delayCost evaluation work) :
    ∃ evaluation : ContinuationEvaluation continuation value outcome, ContinuationWork delayCost evaluation work := by
  cases continuation with
  | one k => obtain ⟨_, cost⟩ := cost; exact ⟨_, .one cost⟩
  | append first rest => exact ContinuationWork.of_viewLAppend first rest value cost

theorem ContinuationWork.of_apply {α β : Type}
    (continuation : ArrsF (Control m) α β) (value : α)
    {outcome : Except CloudError β} {work}
    {evaluation : Evaluation (ArrsF.apply continuation value) outcome}
    (cost : ProgramWork delayCost evaluation work) :
    ∃ result : ContinuationEvaluation continuation value outcome, ContinuationWork delayCost result work := by
  apply ContinuationWork.of_viewL continuation value
  have witnessed : ∃ h : Evaluation (ArrsF.apply continuation value) outcome,
      ProgramWork delayCost h work := ⟨evaluation, cost⟩
  cases view : ArrsF.viewL continuation with
  | one k =>
    rw [ArrsF.apply, view] at witnessed
    exact witnessed
  | cons k rest =>
    rw [ArrsF.apply, view] at witnessed
    obtain ⟨_, cost⟩ := witnessed
    rcases cost.bind_cases (k value) (ArrsF.apply rest) with success | failure
    · obtain ⟨next, firstWork, restWork, head, tail, headCost, tailCost, rfl⟩ := success
      obtain ⟨_, restCost⟩ := ContinuationWork.of_apply rest next tailCost
      exact ⟨_, .success (.one headCost) restCost⟩
    · obtain ⟨error, head, headCost, rfl⟩ := failure
      exact ⟨_, .failure rest (.one headCost)⟩
termination_by sizeOf continuation
decreasing_by simpa [view] using ArrsF.viewL_rest_lt continuation

/-- A continuation can also be rebuilt in the forward direction. Its work is
fixed by the existing inverse theorem and uniqueness, so no second queue
normalization proof is needed. -/
theorem ContinuationWork.apply {continuation : ArrsF (Control m) α β} {value outcome work}
    {evaluation : ContinuationEvaluation continuation value outcome}
    (cost : ContinuationWork delayCost evaluation work) (supported : PureContinuation continuation) :
    ∃ result : Evaluation (ArrsF.apply continuation value) outcome, ProgramWork delayCost result work := by
  obtain ⟨_, result⟩ := Evaluation.exists (ArrsF.apply continuation value) (supported.apply value)
  obtain ⟨_, resultCost⟩ := result.work_exists delayCost
  obtain ⟨_, originalCost⟩ := ContinuationWork.of_apply continuation value resultCost
  obtain ⟨rfl, rfl⟩ := cost.unique originalCost
  exact ⟨result, resultCost⟩

theorem returnWork_map (outcome : Except CloudError α) (f : α → β) :
    returnWork (outcome.map f) = returnWork outcome := by cases outcome <;> rfl

/-- Encoding a branch result changes its returned value but adds no work. -/
theorem ProgramWork.map {program : Cloud m α} {outcome work}
    {evaluation : Evaluation program outcome} (cost : ProgramWork delayCost evaluation work)
    (supported : PureProgram program) (f : α → β) :
    ∃ result : Evaluation (f <$> program) (outcome.map f), ProgramWork delayCost result work := by
  obtain ⟨_, evaluation⟩ := Evaluation.exists (f <$> program) (supported.map f)
  obtain ⟨_, mappedCost⟩ := evaluation.work_exists delayCost
  obtain ⟨original, source, sourceCost, same⟩ := mappedCost.map_cases program f
  obtain ⟨rfl, rfl⟩ := sourceCost.unique cost
  subst same
  exact ⟨evaluation, mappedCost⟩

theorem ContinuationEvaluation.of_apply {continuation : ArrsF (Control m) α β} {value outcome}
    (evaluation : Evaluation (ArrsF.apply continuation value) outcome) :
    ContinuationEvaluation continuation value outcome := by
  obtain ⟨_, cost⟩ := evaluation.work_exists
  exact (ContinuationWork.of_apply continuation value cost).choose

end LeanCloud.Proofs
