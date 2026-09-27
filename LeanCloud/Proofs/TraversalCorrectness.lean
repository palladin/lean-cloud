import LeanCloud.Proofs.ControlTraversal

/-! Whole-language traversal by strong induction on finite direct evaluation.
Parallel children and a successful request's continuation have strictly smaller
work measures. Reconstruction fuel is supplied by the traversal certificates. -/

namespace LeanCloud.Proofs.ReplayModel
open Lean LeanEff

/-- Every finite supported evaluation can be traversed inside any certified
enclosing workflow, with the same outcome and external-world transition. -/
theorem Evaluation.traverse {World : Type} {blobs : BlobModel World}
    {program : Cloud (StateM World) Json} {world finalWorld : World}
    {outcome : Except CloudError Json} {work : Nat}
    (execution : Evaluation blobs program world outcome finalWorld work) :
    CanTraverse blobs program world outcome finalWorld := by
  induction work using Nat.strongRecOn generalizing program world outcome finalWorld with
  | ind work ih =>
    have smaller : ∀ {program : Cloud (StateM World) Json} {world finalWorld : World}
        {outcome : Except CloudError Json} {smallWork : Nat},
        Evaluation blobs program world outcome finalWorld smallWork → smallWork < work →
        CanTraverse blobs program world outcome finalWorld := by
      intro program world finalWorld outcome smallWork traced less
      exact ih smallWork less traced
    intro root start journal steps route fresh
    have nonempty : 0 < start.size := by have := route.depth_le; simp only [Location.size_root] at this; omega
    cases execution with
    | pure value world => exact ⟨BranchTraversal.of_pure value steps route fresh⟩
    | success control rest =>
      obtain ⟨reduction⟩ := ControlEvaluation.traverse control smaller (by omega) route fresh
      obtain ⟨nextFresh, nextRoute⟩ := reduction.ready
      have positive := control.positive
      obtain ⟨tail⟩ := smaller rest.apply (by omega) root reduction.location reduction.finalJournal
        reduction.nextSteps nextRoute nextFresh
      exact ⟨BranchTraversal.prepend reduction.sameDepth reduction.sameParent
        reduction.completed reduction.ancestors reduction.correct tail⟩
    | failure continuation control =>
      obtain ⟨reduction⟩ := ControlEvaluation.traverse control smaller (by omega) route fresh
      exact ⟨{
        location := reduction.location
        finalJournal := reduction.finalJournal
        nonempty := reduction.nonempty
        sameDepth := reduction.sameDepth
        sameParent := reduction.sameParent
        ready := reduction.ready
        completed := reduction.completed
        ancestors := reduction.ancestors
        correct := reduction.correct
      }⟩

end LeanCloud.Proofs.ReplayModel
