import LeanCloud.Proofs.Traversal

/-! A finite plan for traversing the remaining children in order. Each child
supplies its traversal proof, retaining the original branch function and index.
`ChildrenEvaluation.pending` builds the plan from direct evaluation. -/

namespace LeanCloud.Proofs
open Lean LeanEff

inductive PendingChildren {World α : Type} (blobs : BlobModel World) (codec : Codec α)
    {count : Nat} (branches : Fin count → Cloud (StateM World) α) :
    Nat → World → Array (Except CloudError α) → World → Prop where
  | done (world : World) : PendingChildren blobs codec branches count world #[] world
  | next {index : Nat} (inside : index < count) {world middle finalWorld : World}
      {outcome : Except CloudError α} {outcomes : Array (Except CloudError α)}
      (traverse : CanTraverse blobs (codec.encode <$> branches ⟨index, inside⟩) world (outcome.map codec.encode) middle)
      (rest : PendingChildren blobs codec branches (index + 1) middle outcomes finalWorld) :
      PendingChildren blobs codec branches index world (#[outcome] ++ outcomes) finalWorld

theorem PendingChildren.size {World α : Type} {blobs : BlobModel World} {codec : Codec α}
    {count index : Nat} {branches : Fin count → Cloud (StateM World) α} {world finalWorld : World}
    {outcomes : Array (Except CloudError α)}
    (pending : PendingChildren blobs codec branches index world outcomes finalWorld) :
    index + outcomes.size = count := by
  induction pending with
  | done => simp
  | next inside traverse rest ih =>
    simp only [Array.size_append, Array.size_singleton]
    omega

/-- The finite evaluation derivation supplies a plan when traversal is available
for strictly smaller work measures. This is the induction step needed by the
whole-language traversal theorem. -/
theorem ChildrenEvaluation.pending {World α : Type} {blobs : BlobModel World} (codec : Codec α)
    {length : Nat} {children : Fin length → Cloud (StateM World) α} {world finalWorld : World}
    {outcomes : Array (Except CloudError α)} {work : Nat}
    (execution : ChildrenEvaluation blobs children world outcomes finalWorld work)
    {limit : Nat}
    (traverse : ∀ {program : Cloud (StateM World) Json} {world finalWorld : World}
      {outcome : Except CloudError Json} {work : Nat},
      Evaluation blobs program world outcome finalWorld work → work < limit →
      CanTraverse blobs program world outcome finalWorld)
    (smaller : work < limit) {count : Nat} (branches : Fin count → Cloud (StateM World) α)
    (offset : Nat) (range : offset + length = count)
    (aligned : ∀ index : Fin length,
      children index = branches ⟨offset + index.val, by have := index.isLt; omega⟩) :
    PendingChildren blobs codec branches offset world outcomes finalWorld := by
  match execution with
  | .empty children world =>
    have equal : offset = count := by simpa using range
    subst offset
    exact .done world
  | .cons head tail =>
    have atHead := aligned 0
    simp only [Fin.val_zero, Nat.add_zero] at atHead
    have headTrace := head.map codec.encode
    rw [atHead] at headTrace
    refine .next (by omega) (traverse headTrace (by omega)) ?_
    apply ChildrenEvaluation.pending codec tail traverse (by omega) branches (offset + 1) (by omega)
    intro index
    rw [aligned index.succ]
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
termination_by structural execution

end LeanCloud.Proofs
