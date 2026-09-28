import LeanCloud.Proofs.SnapshotWork
import LeanCloud.Proofs.PureContinuation

/-! A partial replay snapshot cannot consume more work than the completed pure
program. An unfinished snapshot always has at least one processing step left. -/
namespace LeanCloud.Proofs
open Lean LeanEff

def unfinishedWork : Option α → Nat
  | none => 1
  | some _ => 0

mutual
  theorem SnapshotWork.extend {journal : Journal} {program : Cloud Id Json}
      {parent branch command status pending spent}
      {snapshot : ReplaySnapshot journal program parent branch command status pending}
      (cost : SnapshotWork snapshot spent) (supported : PureProgram program) :
      ∃ outcome work, (∃ evaluation : Evaluation program outcome, ProgramWork 0 evaluation work) ∧
        spent + unfinishedWork status ≤ work + returnWork outcome := by
    match cost with
    | .pending .. =>
      obtain ⟨outcome, evaluation⟩ := Evaluation.exists program supported
      obtain ⟨work, cost⟩ := evaluation.work_exists
      exact ⟨outcome, work, ⟨_, cost⟩, cost.total_positive⟩
    | .returned value _ => exact ⟨.ok value, 0, ⟨_, .pure value⟩, by simp [unfinishedWork, returnWork]⟩
    | .failed error continuation _ =>
      exact ⟨.error error, 1, ⟨_, .failure continuation (.fail error)⟩, by simp [unfinishedWork, returnWork]⟩
    | .delay rest =>
      obtain ⟨outcome, work, ⟨_, remaining⟩, bound⟩ := rest.extend (supported.2.apply ())
      obtain ⟨_, restCost⟩ := ContinuationWork.of_apply _ () remaining
      exact ⟨outcome, 0 + work, ⟨_, .success .delay restCost⟩, by omega⟩
    | .parallel (codec := codec) (continuation := continuation) children _ _ =>
      obtain ⟨outcomes, childrenWork, ⟨_, childrenCost⟩, bound⟩ := children.extend supported.1.2
      cases collected : outcomes.mapM id with
      | error error =>
        obtain ⟨_, controlCost⟩ := childrenCost.control codec collected
        exact ⟨.error error, childrenWork + 2, ⟨_, .failure continuation controlCost⟩,
          by simp only [unfinishedWork, returnWork]; omega⟩
      | ok values =>
        obtain ⟨outcome, remaining⟩ := Evaluation.exists (ArrsF.apply continuation values) (supported.2.apply values)
        obtain ⟨restWork, restCost⟩ := remaining.work_exists
        obtain ⟨_, controlCost⟩ := childrenCost.control codec collected
        obtain ⟨_, continuationCost⟩ := ContinuationWork.of_apply _ _ restCost
        exact ⟨outcome, childrenWork + 2 + restWork,
          ⟨_, .success controlCost continuationCost⟩,
          by simp only [unfinishedWork]; omega⟩
    | .parallelSuccess (codec := codec) (childrenWork := childrenWork) first collected _ rest =>
      obtain ⟨outcome, work, ⟨_, remaining⟩, bound⟩ := rest.extend (supported.2.apply _)
      obtain ⟨_, controlCost⟩ := first.control codec collected
      obtain ⟨_, restCost⟩ := ContinuationWork.of_apply _ _ remaining
      exact ⟨outcome, childrenWork + 2 + work,
        ⟨_, .success controlCost restCost⟩, by omega⟩
    | .parallelFailure (codec := codec) (error := error) (childrenWork := childrenWork) continuation children collected _ =>
      obtain ⟨_, controlCost⟩ := children.control codec collected
      exact ⟨.error error, childrenWork + 2, ⟨_, .failure continuation controlCost⟩,
        by simp [unfinishedWork, returnWork]⟩
  termination_by structural cost

  theorem ChildrenSnapshotWork.extend {α : Type} {journal : Journal} {codec : Codec α} {count : Nat}
      {branches : Fin count → Cloud Id α} {parent offset statuses pending spent}
      {snapshot : ChildSnapshots journal codec branches parent offset statuses pending}
      (cost : ChildrenSnapshotWork snapshot spent) (supported : ∀ index, PureProgram (branches index)) :
      ∃ outcomes work, (∃ evaluation : ChildrenEvaluation branches outcomes, ChildrenWork 0 evaluation work) ∧ spent ≤ work := by
    match cost with
    | .empty codec branches _ _ => exact ⟨#[], 0, ⟨_, .empty branches⟩, by omega⟩
    | .cons head tail =>
      obtain ⟨encoded, firstWork, ⟨_, headCost⟩, headBound⟩ := head.extend ((supported 0).map codec.encode)
      obtain ⟨outcome, _, originalCost, same⟩ := headCost.map_cases (branches 0) codec.encode
      obtain ⟨outcomes, restWork, ⟨_, restCost⟩, tailBound⟩ := tail.extend (fun index => supported index.succ)
      refine ⟨#[outcome] ++ outcomes, firstWork + returnWork outcome + restWork, ⟨_, .cons originalCost restCost⟩, ?_⟩
      rw [same, returnWork_map] at headBound
      omega
  termination_by structural cost
end

theorem SnapshotWork.bounded {program : Cloud Id Json} {outcome total}
    {canonical : Evaluation program outcome} (totalCost : ProgramWork 0 canonical total)
    {journal parent branch command status pending spent}
    {snapshot : ReplaySnapshot journal program parent branch command status pending}
    (cost : SnapshotWork snapshot spent) (supported : PureProgram program) :
    spent + unfinishedWork status ≤ total + returnWork outcome := by
  obtain ⟨_, _, ⟨_, completion⟩, bound⟩ := cost.extend supported
  obtain ⟨rfl, rfl⟩ := totalCost.unique completion
  exact bound

end LeanCloud.Proofs
