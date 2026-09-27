import LeanCloud.Proofs.ReplayCompletion
import LeanCloud.Proofs.Evaluation

namespace LeanCloud.Proofs.ReplayModel
open Lean LeanEff ReplayInterpreter.Internal

abbrev encoded (outcome : Except CloudError Json) : Exit :=
  encodeOutcome (inferInstance : Codec Json) outcome

structure BranchTraversal {World : Type} (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (start : Location) (journal : Journal) (world : World)
    (outcome : Except CloudError Json) (finalWorld : World) where
  location : Location
  finalJournal : Journal
  nonempty : 0 < location.size
  sameDepth : location.size = start.size
  sameParent : location.parent? = start.parent?
  ready : ReturnReady finalJournal location (encoded outcome)
  completed : journal.PreservesCompleted finalJournal
  ancestors : journal.PreservesAncestors finalJournal start
  correct : ∀ (parent : Parent) (rest : List Location), parent.Valid start journal →
    Segment blobs root ⟨journal, start :: rest, none⟩ world
      (parent.after finalJournal location (encoded outcome) rest) finalWorld

def CanTraverse {World : Type} (blobs : BlobModel World) (program : Cloud (StateM World) Json)
    (world : World) (outcome : Except CloudError Json) (finalWorld : World) : Prop :=
  ∀ (root : Cloud (StateM World) Json) (start : Location) (journal : Journal) (steps : Nat),
    ReplayRoute journal root Location.root program start steps → journal.Fresh start →
    Nonempty (BranchTraversal blobs root start journal world outcome finalWorld)

namespace BranchTraversal

variable {World : Type} {blobs : BlobModel World} {root : Cloud (StateM World) Json}
    {start : Location} {journal : Journal} {world : World}

def of_pure (value : Json) (steps : Nat)
    (route : ReplayRoute journal root Location.root (.pure value) start steps)
    (fresh : journal.Fresh start) : BranchTraversal blobs root start journal world (.ok value) world where
  location := start
  finalJournal := journal
  nonempty := by have := route.depth_le; simp only [Location.size_root] at this; omega
  sameDepth := rfl
  sameParent := rfl
  ready := .fresh fresh
  completed := .refl _
  ancestors := .refl _ _
  correct := by
    intro parent rest valid
    exact report_segment blobs root (.pure value) parent start (.success value) journal world rest steps
      route (.fresh fresh) valid (fun _ => by simp only [walk, beq_self_eq_true, ↓reduceIte])

def of_failure {α : Type} (error : CloudError) (continuation : ArrsF (Control (StateM World)) α Json)
    (steps : Nat) (route : ReplayRoute journal root Location.root (.impure (.fail error) continuation) start steps)
    (fresh : journal.Fresh start) : BranchTraversal blobs root start journal world (.error error) world where
  location := start
  finalJournal := journal
  nonempty := by have := route.depth_le; simp only [Location.size_root] at this; omega
  sameDepth := rfl
  sameParent := rfl
  ready := .fresh fresh
  completed := .refl _
  ancestors := .refl _ _
  correct := by
    intro parent rest valid
    exact report_segment blobs root _ parent start (.failure error) journal world rest steps
      route (.fresh fresh) valid (fun _ => by simp only [walk, beq_self_eq_true, ↓reduceIte])

def prepend {nextLocation : Location} {nextJournal : Journal} {nextWorld finalWorld : World}
    {outcome : Except CloudError Json}
    (depth : nextLocation.size = start.size) (sameParent : nextLocation.parent? = start.parent?)
    (completed : journal.PreservesCompleted nextJournal)
    (ancestors : journal.PreservesAncestors nextJournal start)
    (advance : ∀ (parent : Parent) (rest : List Location), parent.Valid start journal →
      Segment blobs root ⟨journal, start :: rest, none⟩ world ⟨nextJournal, nextLocation :: rest, none⟩ nextWorld)
    (tail : BranchTraversal blobs root nextLocation nextJournal nextWorld outcome finalWorld) :
    BranchTraversal blobs root start journal world outcome finalWorld where
  location := tail.location
  finalJournal := tail.finalJournal
  nonempty := tail.nonempty
  sameDepth := tail.sameDepth.trans depth
  sameParent := tail.sameParent.trans sameParent
  ready := tail.ready
  completed := completed.trans tail.completed
  ancestors := ancestors.trans (tail.ancestors.of_depth_le (by omega))
  correct := by
    intro parent rest valid
    exact (advance parent rest valid).trans (tail.correct parent rest (valid.preserve sameParent ancestors))

def of_sequential_failure {α : Type} (codec : Codec α) (operation : Operation (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) α Json) (error : CloudError) (nextWorld : World)
    (steps : Nat) (route : ReplayRoute journal root Location.root (.impure (.sequential codec operation) continuation) start steps)
    (fresh : journal.Fresh start)
    (executed : ((modelStorage blobs).execute operation).run Journal.empty world =
      ((.error error, Journal.empty), nextWorld)) :
    BranchTraversal blobs root start journal world (.error error) nextWorld where
  location := start
  finalJournal := journal
  nonempty := by have := route.depth_le; simp only [Location.size_root] at this; omega
  sameDepth := rfl
  sameParent := rfl
  ready := .fresh fresh
  completed := .refl _
  ancestors := .refl _ _
  correct := by
    intro parent rest valid
    apply Segment.one (bound := steps + 1)
    intro fuel enough
    have nonempty : 0 < start.size := by have := route.depth_le; simp only [Location.size_root] at this; omega
    have operationRun : ((storage blobs).execute operation).run ⟨journal, start :: rest, none⟩ world =
        ((.error error, ⟨journal, start :: rest, none⟩), nextWorld) := by rw [execute, executed]
    rw [show fuel = (fuel - steps - 1 + 1) + steps by omega,
      route.from_root valid.openParent,
      walk_fresh_sequential_failure blobs _ codec operation continuation error start _ world nextWorld
        (fresh.missing nonempty) operationRun]
    exact finish_ready blobs parent start (.failure error) journal _ nextWorld nonempty (.fresh fresh) valid

end BranchTraversal
end LeanCloud.Proofs.ReplayModel
