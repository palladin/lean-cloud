import LeanCloud.Proofs.Driver
import LeanCloud.Proofs.Evaluation
import LeanCloud.Proofs.ParallelSlots

/-! Compositional branch traversal. A certificate stops immediately before the
branch's terminal completion, leaving the real driver free to resume its parent.
The positive residual fuel accounts for that final completion step. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

def terminalProgram {m : Type → Type} : Except CloudError Json → Cloud m Json
  | .ok value => .pure value
  | .error error => .impure (.fail (α := Unit) error) (.one fun _ => .pure Json.null)

theorem terminalProgram_terminal {m : Type → Type} (outcome : Except CloudError Json) :
    Terminal (terminalProgram (m := m) outcome) (encodeOutcome (inferInstance : Codec Json) outcome) := by
  cases outcome with
  | ok value => exact .success value
  | error error => exact .failure error _

theorem encode_mapped_outcome (codec : Codec α) (outcome : Except CloudError α) :
    encodeOutcome (inferInstance : Codec Json) (outcome.map codec.encode) = encodeOutcome codec outcome := by
  cases outcome <;> rfl

/-- A terminal failure may already have been recorded by a completed group.
Fresh terminal returns never require comparing successful JSON values. -/
inductive ReturnReady (journal : Journal) (location : Location) : Except CloudError Json → Prop where
  | fresh {outcome} (available : journal.Fresh location) : ReturnReady journal location outcome
  | failure (error : CloudError)
      (recorded : journal location.key = some (toJson (Result.completed (.failure error))))
      (available : journal.Fresh location.next) : ReturnReady journal location (.error error)

namespace ReturnReady

variable {journal : Journal} {location parent : Location} {index : Nat} {outcome : Except CloudError Json}

theorem preserves_completed (ready : ReturnReady journal location outcome)
    (hasParent : location.parent? = some (parent, index)) (children : Array (Option Exit))
    (recorded : journal parent.key = some (toJson (Result.suspended children))) :
    journal.PreservesCompleted
      (journal.completeChild location parent children index (encodeOutcome (inferInstance : Codec Json) outcome)) := by
  cases ready with
  | fresh available =>
    obtain ⟨nonempty, depth⟩ := Location.parent_size hasParent
    exact journal.completeChild_preserves _ _ _ _ _ hasParent (available.missing (by omega)) recorded
  | failure error ownResult available =>
    exact journal.completeChild_preserves_existing _ _ _ _ _ ownResult recorded

/-- Both fresh returns and recorded failures leave later commands untouched. -/
theorem fresh_next (ready : ReturnReady journal location outcome) (nonempty : 0 < location.size) :
    journal.Fresh location.next := by
  cases ready with
  | fresh available => exact available.advance (Location.earlier_next location nonempty)
  | failure _ _ available => exact available

theorem fresh_sibling (ready : ReturnReady journal location outcome)
    (hasParent : location.parent? = some (parent, index)) (children : Array (Option Exit)) :
    (journal.completeChild location parent children index (encodeOutcome (inferInstance : Codec Json) outcome)).Fresh
      (parent.child (index + 1)) := by
  have depth := Location.parent_size hasParent
  exact (ready.fresh_next (by omega)).complete_child hasParent
    (Location.earlier_next_sibling (Location.next_parent hasParent)) children _

theorem fresh_parent_next (ready : ReturnReady journal location outcome)
    (hasParent : location.parent? = some (parent, index)) (children : Array (Option Exit)) :
    (journal.completeChild location parent children index (encodeOutcome (inferInstance : Codec Json) outcome)).Fresh
      parent.next := by
  have depth := Location.parent_size hasParent
  exact (ready.fresh_next (by omega)).complete_child hasParent
    (Location.earlier_parent_next (Location.next_parent hasParent)) children _

/-- The same completion equation applies to a fresh terminal result and to a
failure already recorded by a nested group. -/
theorem walk_child {World : Type} (blobs : BlobModel World) (root : Cloud (StateM World) Json)
    (ready : ReturnReady journal location outcome) (fuel : Nat) (world : World)
    (hasParent : location.parent? = some (parent, index)) (children : Array (Option Exit))
    (recorded : journal parent.key = some (toJson (Result.suspended children)))
    (inside : index < children.size) (slotMissing : children[index]! = none) :
    let encoded := encodeOutcome (inferInstance : Codec Json) outcome
    let updated := Result.settle (children.set! index (some encoded))
    let committed := journal.completeChild location parent children index encoded
    (step.walk (modelStorage blobs) root (fuel + 1) (terminalProgram outcome) location location).run journal world =
      match updated with
      | .suspended _ => ((.ok (.suspended parent fuel), committed), world)
      | .completed _ => (step.walk (modelStorage blobs) root fuel root Location.root parent).run committed world := by
  cases ready with
  | fresh available =>
    obtain ⟨nonempty, depth⟩ := Location.parent_size hasParent
    exact walk_terminal_child blobs root _ _ (terminalProgram_terminal outcome) fuel location location parent index
      journal world children (by simp [Location.before]) hasParent (available.missing (by omega)) recorded inside slotMissing
  | failure error ownResult available =>
    exact walk_recorded_failure_child blobs root error _ fuel location location parent index journal world children
      (by simp [Location.before]) hasParent ownResult recorded inside slotMissing

end ReturnReady

/-- Finite execution of one branch before it reports its result to its parent.
All changes retain the parent's records and already completed work. -/
structure BranchTraversal {World β : Type} [Codec β] (blobs : BlobModel World)
    (root program : Cloud (StateM World) Json) (start : Location) (journal : Journal) (world : World)
    (outcome : Except CloudError Json) (finalWorld : World) where
  location : Location
  finalJournal : Journal
  cost : Nat
  nonempty : 0 < location.size
  sameDepth : location.size = start.size
  sameParent : location.parent? = start.parent?
  ready : ReturnReady finalJournal location outcome
  completed : journal.PreservesCompleted finalJournal
  ancestors : journal.PreservesAncestors finalJournal start
  correct : ∀ fuel, 0 < fuel →
    (driveWalk (α := β) blobs (fuel + cost) root program start start).run journal world =
      (driveWalk (α := β) blobs fuel root (terminalProgram outcome) location location).run finalJournal finalWorld

/-- Traversability in any certified enclosing workflow. The result codec belongs
to that enclosing workflow; the traversed branch itself returns encoded JSON. -/
def CanTraverse {World : Type} (blobs : BlobModel World) (program : Cloud (StateM World) Json)
    (world : World) (outcome : Except CloudError Json) (finalWorld : World) : Prop :=
  ∀ {β : Type} [Codec β] (root : Cloud (StateM World) Json) (start : Location) (journal : Journal) (steps : Nat),
    ReplayRoute journal root Location.root program start steps → journal.Fresh start →
    Nonempty (BranchTraversal (β := β) blobs root program start journal world outcome finalWorld)

theorem driveWalk_failure {World α β : Type} [Codec β] (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat) (error : CloudError)
    (continuation : ArrsF (Control (StateM World)) α Json) (current target : Location) :
    driveWalk (α := β) blobs fuel root (.impure (.fail error) continuation) current target =
      driveWalk blobs fuel root (terminalProgram (.error error)) current target := by
  cases fuel <;> rfl

namespace BranchTraversal

variable {World β : Type} [Codec β] {blobs : BlobModel World}
    {root : Cloud (StateM World) Json} {start : Location} {journal : Journal} {world : World}

def of_pure (value : Json) (nonempty : 0 < start.size) (fresh : journal.Fresh start) :
    BranchTraversal (β := β) blobs root (.pure value) start journal world (.ok value) world where
  location := start
  finalJournal := journal
  cost := 0
  nonempty := nonempty
  sameDepth := rfl
  sameParent := rfl
  ready := .fresh fresh
  completed := .refl _
  ancestors := .refl _ _
  correct := by intro fuel positive; rfl

/-- Concatenate a proved runtime segment with a remaining branch traversal.
Only the segment's actual state changes and consumed fuel enter the certificate. -/
def prepend {program next : Cloud (StateM World) Json} {nextLocation : Location}
    {nextJournal : Journal} {nextWorld finalWorld : World} {outcome : Except CloudError Json}
    (spent : Nat) (depth : nextLocation.size = start.size) (parent : nextLocation.parent? = start.parent?)
    (completed : journal.PreservesCompleted nextJournal)
    (ancestors : journal.PreservesAncestors nextJournal start)
    (advances : ∀ fuel, 0 < fuel →
      (driveWalk (α := β) blobs (fuel + spent) root program start start).run journal world =
        (driveWalk (α := β) blobs fuel root next nextLocation nextLocation).run nextJournal nextWorld)
    (tail : BranchTraversal (β := β) blobs root next nextLocation nextJournal nextWorld outcome finalWorld) :
    BranchTraversal (β := β) blobs root program start journal world outcome finalWorld where
  location := tail.location
  finalJournal := tail.finalJournal
  cost := spent + tail.cost
  nonempty := tail.nonempty
  sameDepth := tail.sameDepth.trans depth
  sameParent := tail.sameParent.trans parent
  ready := tail.ready
  completed := completed.trans tail.completed
  ancestors := ancestors.trans (tail.ancestors.of_depth_le (by omega))
  correct := by
    intro fuel positive
    have advance := advances (fuel + tail.cost) (by omega)
    have finish := tail.correct fuel positive
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using advance.trans finish

def of_sequential_failure {α : Type} {codec : Codec α} {operation : Operation (StateM World) α}
    {continuation : ArrsF (Control (StateM World)) α Json} {error : CloudError} {nextWorld : World}
    (nonempty : 0 < start.size) (fresh : journal.Fresh start)
    (executed : ((modelStorage blobs).execute operation).run journal world = ((.error error, journal), nextWorld)) :
    BranchTraversal (β := β) blobs root (.impure (.sequential codec operation) continuation)
      start journal world (.error error) nextWorld where
  location := start
  finalJournal := journal
  cost := 0
  nonempty := nonempty
  sameDepth := rfl
  sameParent := rfl
  ready := .fresh fresh
  completed := .refl _
  ancestors := .refl _ _
  correct := by
    intro fuel positive
    obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    have reduced := walk_fresh_sequential_failure blobs root rest codec operation continuation error start start
      journal world nextWorld (by simp [Location.before]) (fresh.missing nonempty) executed
    have driven := driveWalk_reduce (α := β) blobs (rest + 1) (rest + 1) root _ _ start start start start
      journal journal world nextWorld (by omega) reduced
    simpa only [Nat.add_zero, driveWalk_failure] using driven

end BranchTraversal
end LeanCloud.Proofs
