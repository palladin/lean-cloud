import LeanCloud.Proofs.PendingChildren

/-! Traversal of a group's pending children, retaining the original branches and
using the real driver's work-item selection and parent reconstruction. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

/-- The real driver at an unfinished child, or the inner loop at a fully
completed parent. This nonrecursive expression marks the two group boundaries. -/
def groupEntry {World α β : Type} [Codec β] (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json)
    (parent : Location) (index fuel : Nat) : ExceptT CloudError (StateT Journal (StateM World)) β :=
  if index < count then LeanCloud.interpret.run (modelStorage blobs) fuel root (parent.child index)
  else driveWalk blobs fuel root (.impure (.parallel codec count branches) continuation) parent parent

def childCompletionCost (count nextIndex prefixSteps : Nat) : Nat :=
  if nextIndex < count then 1 else prefixSteps + 1

/-- Completing a child reaches precisely the next group boundary. The last
child pays for rebuilding the parent; earlier children return to the queue. -/
theorem ReturnReady.drive_group_next {World α β : Type} [Codec β]
    {blobs : BlobModel World} {journal : Journal} {root : Cloud (StateM World) Json}
    {codec : Codec α} {count : Nat} {branches : Fin count → Cloud (StateM World) α}
    {continuation : ArrsF (Control (StateM World)) (Array α) Json}
    {parent location : Location} {steps : Nat}
    (route : ReplayRoute journal root Location.root
      (.impure (.parallel codec count branches) continuation) parent steps)
    (past : Array (Except CloudError α)) (outcome : Except CloudError α)
    (inside : past.size < count)
    (ready : ReturnReady journal location (outcome.map codec.encode))
    (hasParent : location.parent? = some (parent, past.size))
    (recorded : journal parent.key = some (toJson (Result.suspended (parallelSlots codec count past))))
    (fuel : Nat) (world : World) :
    let committed := journal.completeChild location parent (parallelSlots codec count past) past.size
      (encodeOutcome codec outcome)
    (driveWalk (α := β) blobs (fuel + childCompletionCost count (past.size + 1) steps) root
      (terminalProgram (outcome.map codec.encode)) location location).run journal world =
      (groupEntry blobs root codec count branches continuation parent (past.size + 1) fuel).run committed world := by
  dsimp only
  let committed := journal.completeChild location parent (parallelSlots codec count past) past.size
    (encodeOutcome codec outcome)
  have slotsInside : past.size < (parallelSlots codec count past).size := by
    rw [parallelSlots_size codec count past (by omega)]
    exact inside
  have slotMissing := parallelSlots_get_pending codec count past past.size (by omega) inside
  have nextRecorded : committed parent.key =
      some (toJson (Result.settle (parallelSlots codec count (past.push outcome)))) := by
    dsimp only [committed]
    rw [Journal.completeChild_records_parent, parallelSlots_update codec count past inside outcome]
  by_cases more : past.size + 1 < count
  · have waiting := parallelSlots_waits codec count (past.push outcome) (by simpa using more)
    have finished := ready.walk_child blobs root fuel world hasParent (parallelSlots codec count past)
      recorded slotsInside slotMissing
    simp only [encode_mapped_outcome, parallelSlots_update codec count past inside outcome, waiting] at finished
    rw [waiting] at nextRecorded
    simp only [childCompletionCost, more, ↓reduceIte, groupEntry]
    exact driveWalk_suspended (α := β) blobs (fuel + 1) fuel root _ location location parent journal committed
      world world (parallelSlots codec count (past.push outcome)) (past.size + 1) finished nextRecorded
      (by simpa using parallelSlots_select codec count (past.push outcome) (by simpa using more)) (by omega)
  · have full : (past.push outcome).size = count := by simp only [Array.size_push]; omega
    obtain ⟨result, settled⟩ := Result.settle_all_completed ((past.push outcome).map (encodeOutcome codec))
    have complete : Result.settle (parallelSlots codec count (past.push outcome)) = .completed result := by
      rw [← full, parallelSlots_full]
      exact settled
    have finished := ready.walk_child blobs root (fuel + steps) world hasParent (parallelSlots codec count past)
      recorded slotsInside slotMissing
    simp only [encode_mapped_outcome, parallelSlots_update codec count past inside outcome, complete] at finished
    have preserved := ready.preserves_completed hasParent (parallelSlots codec count past) recorded
    simp only [encode_mapped_outcome] at preserved
    have parentRoute := route.preserve preserved
      (journal.completeChild_preserves_ancestors location parent (parallelSlots codec count past) past.size
        (encodeOutcome codec outcome) hasParent)
    have reconstructed := parentRoute.reconstruct (blobs := blobs) root fuel world
    have reduced := finished.trans reconstructed
    simp only [childCompletionCost, more, ↓reduceIte, groupEntry]
    have driven := driveWalk_reduce (α := β) blobs (fuel + steps + 1) fuel root _ _ location location parent parent
      journal committed world world (by omega) reduced
    simpa only [Nat.add_assoc] using driven

/-- Process all pending children and stop at the completed parent, before its
continuation or failure is selected. -/
structure GroupTraversal {World α β : Type} [Codec β] (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json)
    (parent : Location) (journal : Journal) (past outcomes : Array (Except CloudError α))
    (world finalWorld : World) where
  finalJournal : Journal
  cost : Nat
  recorded : finalJournal parent.key =
    some (toJson (Result.settle (parallelSlots codec count (past ++ outcomes))))
  fresh : finalJournal.Fresh parent.next
  completed : journal.PreservesCompleted finalJournal
  ancestors : journal.PreservesAncestors finalJournal parent
  correct : ∀ fuel, 0 < fuel →
    (groupEntry (β := β) blobs root codec count branches continuation parent past.size (fuel + cost)).run journal world =
      (driveWalk (α := β) blobs fuel root (.impure (.parallel codec count branches) continuation) parent parent).run
        finalJournal finalWorld

/-- Finite pending-child plans are executable by the real driver. Each induction
step traverses one child, commits its result, and follows the actual next work
item or parent reconstruction. -/
theorem PendingChildren.process {World α β : Type} [Codec β] {blobs : BlobModel World} {codec : Codec α}
    {count index : Nat} {branches : Fin count → Cloud (StateM World) α} {world finalWorld : World}
    {outcomes : Array (Except CloudError α)}
    (pending : PendingChildren blobs codec branches index world outcomes finalWorld)
    {root : Cloud (StateM World) Json} {continuation : ArrsF (Control (StateM World)) (Array α) Json}
    {parent : Location} {journal : Journal} {past : Array (Except CloudError α)} {steps : Nat}
    (pastSize : past.size = index)
    (route : ReplayRoute journal root Location.root
      (.impure (.parallel codec count branches) continuation) parent steps)
    (recorded : journal parent.key = some (toJson (Result.settle (parallelSlots codec count past))))
    (available : if past.size < count then journal.Fresh (parent.child past.size) else journal.Fresh parent.next) :
    Nonempty (GroupTraversal (β := β) blobs root codec count branches continuation parent journal past outcomes
      world finalWorld) := by
  match pending with
  | .done world =>
    refine ⟨{
      finalJournal := journal
      cost := 0
      recorded := by simpa using recorded
      fresh := by simpa [pastSize] using available
      completed := .refl _
      ancestors := .refl _ _
      correct := ?_
    }⟩
    intro fuel positive
    simp only [Nat.add_zero, groupEntry, pastSize, Nat.lt_irrefl, ↓reduceIte]
  | @PendingChildren.next _ _ _ _ _ _ index inside world middle finalWorld outcome outcomes traverse rest =>
    have pastInside : past.size < count := by omega
    have parentNonempty : 0 < parent.size := by
      have depth := route.depth_le
      simp only [Location.size_root] at depth
      omega
    have suspended := recorded
    rw [parallelSlots_waits codec count past pastInside] at suspended
    have childRoute := route.enter_child (parallelSlots codec count past) suspended
      (parallelSlots_size codec count past (by omega)) ⟨index, inside⟩
    have childFresh : journal.Fresh (parent.child index) := by simpa [pastSize, inside] using available
    obtain ⟨child⟩ := traverse (β := β) root (parent.child index) journal (steps + 1) childRoute childFresh
    have hasParent : child.location.parent? = some (parent, past.size) := by
      rw [child.sameParent, Location.parent_child parent parentNonempty, pastSize]
    have parentRecorded : child.finalJournal parent.key =
        some (toJson (Result.suspended (parallelSlots codec count past))) := by
      exact (child.ancestors parent parentNonempty (by simp [Location.size_child])).trans suspended
    have parentRoute := route.preserve child.completed
      (child.ancestors.of_depth_le (by simp [Location.size_child]))
    let committed := child.finalJournal.completeChild child.location parent (parallelSlots codec count past)
      past.size (encodeOutcome codec outcome)
    have preserved := child.ready.preserves_completed hasParent (parallelSlots codec count past) parentRecorded
    simp only [encode_mapped_outcome] at preserved
    have keptAncestors := child.finalJournal.completeChild_preserves_ancestors child.location parent
      (parallelSlots codec count past) past.size (encodeOutcome codec outcome) hasParent
    have nextRoute := parentRoute.preserve preserved keptAncestors
    have nextRecorded : committed parent.key =
        some (toJson (Result.settle (parallelSlots codec count (past.push outcome)))) := by
      dsimp only [committed]
      rw [Journal.completeChild_records_parent, parallelSlots_update codec count past pastInside]
    have nextAvailable : if (past.push outcome).size < count then committed.Fresh (parent.child (past.push outcome).size)
        else committed.Fresh parent.next := by
      split
      · simpa only [Array.size_push, encode_mapped_outcome] using
          child.ready.fresh_sibling hasParent (parallelSlots codec count past)
      · simpa only [encode_mapped_outcome] using
          child.ready.fresh_parent_next hasParent (parallelSlots codec count past)
    obtain ⟨tail⟩ := PendingChildren.process (β := β) rest (past := past.push outcome) (journal := committed)
      (by simp [pastSize]) nextRoute nextRecorded nextAvailable
    let spent := childCompletionCost count (past.size + 1) steps
    refine ⟨{
      finalJournal := tail.finalJournal
      cost := steps + 1 + child.cost + spent + tail.cost
      recorded := ?_
      fresh := tail.fresh
      completed := child.completed.trans (preserved.trans tail.completed)
      ancestors := (child.ancestors.of_depth_le (by simp [Location.size_child])).trans
        (keptAncestors.trans tail.ancestors)
      correct := ?_
    }⟩
    · simpa only [Array.push_eq_append, Array.append_assoc] using tail.recorded
    · intro fuel positive
      have entered := childRoute.drive (α := β) (blobs := blobs) (fuel + tail.cost + spent + child.cost) world
      have traversed := child.correct (fuel + tail.cost + spent) (by omega)
      have finished := child.ready.drive_group_next (β := β) (blobs := blobs) parentRoute past outcome pastInside hasParent parentRecorded
        (fuel + tail.cost) middle
      have remaining := tail.correct fuel positive
      have chain := entered.trans (traversed.trans (finished.trans (by
        simpa only [Array.size_push] using remaining)))
      simp only [groupEntry, pastSize, inside, ↓reduceIte]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using chain
termination_by structural pending

/-- A fresh group reaches its completed record before returning values to its
continuation. The certificate includes all child effects and their final world. -/
structure ParallelCompletion {World α β : Type} [Codec β] (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json)
    (parent : Location) (journal : Journal) (outcomes : Array (Except CloudError α)) (world finalWorld : World) where
  finalJournal : Journal
  cost : Nat
  recorded : finalJournal parent.key = some (toJson (Result.settle (parallelSlots codec count outcomes)))
  fresh : finalJournal.Fresh parent.next
  completed : journal.PreservesCompleted finalJournal
  ancestors : journal.PreservesAncestors finalJournal parent
  correct : ∀ fuel, 0 < fuel →
    (driveWalk (α := β) blobs (fuel + cost) root (.impure (.parallel codec count branches) continuation)
      parent parent).run journal world =
      (driveWalk (α := β) blobs fuel root (.impure (.parallel codec count branches) continuation)
        parent parent).run finalJournal finalWorld

theorem PendingChildren.start {World α β : Type} [Codec β] {blobs : BlobModel World} {codec : Codec α}
    {count : Nat} {branches : Fin count → Cloud (StateM World) α} {world finalWorld : World}
    {outcomes : Array (Except CloudError α)}
    (pending : PendingChildren blobs codec branches 0 world outcomes finalWorld)
    {root : Cloud (StateM World) Json} {continuation : ArrsF (Control (StateM World)) (Array α) Json}
    {parent : Location} {journal : Journal} {steps : Nat}
    (law : CodecLaw codec)
    (route : ReplayRoute journal root Location.root
      (.impure (.parallel codec count branches) continuation) parent steps)
    (fresh : journal.Fresh parent) :
    Nonempty (ParallelCompletion (β := β) blobs root codec count branches continuation parent journal outcomes
      world finalWorld) := by
  have nonempty : 0 < parent.size := by have := route.depth_le; simp only [Location.size_root] at this; omega
  have missing := fresh.missing nonempty
  let saved := journal.write parent.key (toJson (Result.settle (parallelSlots codec count #[])))
  have savedRoute := route.record_frontier (toJson (Result.settle (parallelSlots codec count #[]))) missing
  have savedRecord : saved parent.key = some (toJson (Result.settle (parallelSlots codec count #[]))) :=
    journal.read_write _ _
  have available : if (#[] : Array (Except CloudError α)).size < count then saved.Fresh (parent.child 0)
      else saved.Fresh parent.next := by
    split
    · exact fresh.child nonempty 0 _
    · exact fresh.next nonempty _
  obtain ⟨children⟩ := pending.process (β := β) (past := #[]) rfl savedRoute savedRecord available
  let creationCost := if 0 < count then 1 else 0
  have create (fuel : Nat) (positive : 0 < fuel) :
      (driveWalk (α := β) blobs (fuel + creationCost) root
        (.impure (.parallel codec count branches) continuation) parent parent).run journal world =
      (groupEntry (β := β) blobs root codec count branches continuation parent 0 fuel).run saved world := by
    by_cases nonzero : 0 < count
    · have waiting := parallelSlots_waits codec count (#[] : Array (Except CloudError α)) (by simpa using nonzero)
      have stored := savedRecord
      rw [waiting] at stored
      have stepped := walk_fresh_parallel blobs root fuel codec count nonzero branches continuation parent parent
        journal world (by simp [Location.entersChild]) (by simp [Location.before]) missing
      have suspended : (step.walk (modelStorage blobs) root (fuel + 1)
          (.impure (.parallel codec count branches) continuation) parent parent).run journal world =
          ((.ok (.suspended parent fuel), saved), world) := by
        dsimp only [saved]
        rw [waiting, parallelSlots_empty]
        exact stepped
      simp only [creationCost, nonzero, ↓reduceIte, groupEntry]
      exact driveWalk_suspended (α := β) blobs (fuel + 1) fuel root _ parent parent parent journal saved world world
        (parallelSlots codec count #[]) 0 suspended stored
        (by simpa using parallelSlots_select codec count (#[] : Array (Except CloudError α)) (by simpa using nonzero))
        (by omega)
    · have zero : count = 0 := by omega
      subst count
      obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      have stored : saved parent.key = some (toJson (Result.completed (.success (Json.arr #[])))) := by
        simpa only [parallelSlots_empty, Array.replicate_zero, Result.settle_empty] using savedRecord
      have freshStep := walk_fresh_empty_parallel blobs root fuel codec branches continuation parent parent journal world
        (by simp [Location.entersChild]) (by simp [Location.before]) missing
      have savedStep := walk_recorded_parallel blobs root fuel codec law 0 branches continuation #[] parent parent saved
        world (by simp [Location.entersChild]) (by simpa using stored)
      have reduced : (step.walk (modelStorage blobs) root (fuel + 1)
          (.impure (.parallel codec 0 branches) continuation) parent parent).run journal world =
          (step.walk (modelStorage blobs) root (fuel + 1)
            (.impure (.parallel codec 0 branches) continuation) parent parent).run saved world := by
        rw [freshStep, savedStep]
        simp only [saved, parallelSlots_empty, Array.replicate_zero, Result.settle_empty]
      simp only [creationCost, Nat.lt_irrefl, ↓reduceIte, Nat.add_zero, groupEntry]
      exact driveWalk_reduce (α := β) blobs (fuel + 1) (fuel + 1) root _ _ parent parent parent parent
        journal saved world world (by omega) reduced
  refine ⟨{
    finalJournal := children.finalJournal
    cost := creationCost + children.cost
    recorded := by simpa using children.recorded
    fresh := children.fresh
    completed := (journal.preservesCompleted_write_missing _ _ missing).trans children.completed
    ancestors := (journal.write_preserves_shallower parent parent _ nonempty (by omega)).trans children.ancestors
    correct := ?_
  }⟩
  intro fuel positive
  have created := create (fuel + children.cost) (by omega)
  have finished := children.correct fuel positive
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using created.trans finished

end LeanCloud.Proofs
