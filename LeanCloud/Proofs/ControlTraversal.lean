import LeanCloud.Proofs.GroupTraversal

/-! One control request, including all work of a parallel group, reduces to its
original continuation or its terminal failure. Smaller child evaluations supply
the induction hypotheses; the runtime interpreter itself remains unchanged. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

def controlRemainder {World α : Type} (continuation : ArrsF (Control (StateM World)) α Json) :
    Except CloudError α → Cloud (StateM World) Json
  | .ok value => ArrsF.apply continuation value
  | .error error => terminalProgram (.error error)

structure ControlTraversal {World α β : Type} [Codec β] (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (request : Control (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) α Json) (start : Location)
    (journal : Journal) (world : World) (outcome : Except CloudError α) (finalWorld : World) where
  location : Location
  finalJournal : Journal
  cost : Nat
  nextSteps : Nat
  nonempty : 0 < location.size
  sameDepth : location.size = start.size
  sameParent : location.parent? = start.parent?
  ready : match outcome with
    | .ok value => finalJournal.Fresh location ∧
      ReplayRoute finalJournal root Location.root (ArrsF.apply continuation value) location nextSteps
    | .error error => ReturnReady finalJournal location (.error error)
  completed : journal.PreservesCompleted finalJournal
  ancestors : journal.PreservesAncestors finalJournal start
  correct : ∀ fuel, 0 < fuel →
    (driveWalk (α := β) blobs (fuel + cost) root (.impure request continuation) start start).run journal world =
      (driveWalk (α := β) blobs fuel root (controlRemainder continuation outcome) location location).run
        finalJournal finalWorld

theorem ControlEvaluation.traverse {World α β : Type} [Codec β] {blobs : BlobModel World}
    {request : Control (StateM World) α} {world finalWorld : World} {outcome : Except CloudError α} {work : Nat}
    (execution : ControlEvaluation blobs request world outcome finalWorld work) {limit : Nat}
    (smaller : ∀ {program : Cloud (StateM World) Json} {world finalWorld : World}
      {outcome : Except CloudError Json} {work : Nat},
      Evaluation blobs program world outcome finalWorld work → work < limit →
      CanTraverse blobs program world outcome finalWorld)
    (bound : work ≤ limit) {root : Cloud (StateM World) Json}
    {continuation : ArrsF (Control (StateM World)) α Json} {start : Location} {journal : Journal} {steps : Nat}
    (route : ReplayRoute journal root Location.root (.impure request continuation) start steps)
    (fresh : journal.Fresh start) :
    Nonempty (ControlTraversal (β := β) blobs root request continuation start journal world outcome finalWorld) := by
  have nonempty : 0 < start.size := by have := route.depth_le; simp only [Location.size_root] at this; omega
  cases execution with
  | delay world =>
    exact ⟨{
      location := start, finalJournal := journal, cost := 1, nextSteps := steps + 1
      nonempty := nonempty, sameDepth := rfl, sameParent := rfl
      ready := ⟨fresh, route.advance_delay⟩
      completed := .refl _, ancestors := .refl _ _
      correct := fun fuel _ => congrArg (fun action => action.run journal world)
        (driveWalk_delay (α := β) blobs root fuel continuation start start)
    }⟩
  | fail world error =>
    exact ⟨{
      location := start, finalJournal := journal, cost := 0, nextSteps := 0
      nonempty := nonempty, sameDepth := rfl, sameParent := rfl
      ready := .fresh fresh, completed := .refl _, ancestors := .refl _ _
      correct := by intro fuel positive; rw [Nat.add_zero, driveWalk_failure]; rfl
    }⟩
  | @sequential α codec operation world finalWorld outcome law executed =>
    have actual := modelStorage_execute blobs operation journal world
    rw [executed] at actual
    cases outcome with
    | ok value =>
      exact ⟨{
        location := start.next
        finalJournal := journal.write start.key (toJson (Result.completed (.success (codec.encode value))))
        cost := 1, nextSteps := steps + 1
        nonempty := Location.next_nonempty _ nonempty
        sameDepth := Location.size_next _, sameParent := Location.next_parent_eq _
        ready := ⟨fresh.next nonempty _, route.advance_sequential law value (fresh.missing nonempty)⟩
        completed := journal.preservesCompleted_write_missing _ _ (fresh.missing nonempty)
        ancestors := journal.write_preserves_shallower _ _ _ nonempty (by omega)
        correct := fun fuel _ => driveWalk_sequential (β := β) blobs root fuel codec law operation continuation start
          journal world finalWorld value nonempty fresh actual
      }⟩
    | error error =>
      let failed := BranchTraversal.of_sequential_failure (β := β) (root := root) (codec := codec)
        (continuation := continuation) nonempty fresh actual
      exact ⟨{
        location := failed.location, finalJournal := failed.finalJournal, cost := failed.cost, nextSteps := 0
        nonempty := failed.nonempty, sameDepth := failed.sameDepth, sameParent := failed.sameParent
        ready := failed.ready, completed := failed.completed, ancestors := failed.ancestors
        correct := failed.correct
      }⟩
  | @parallel α codec count branches world finalWorld outcomes childWork law children =>
    have pending := children.pending codec smaller (by omega) branches 0 (by omega)
      (by intro index; simp only [Nat.zero_add])
    obtain ⟨group⟩ := pending.start (β := β) law route fresh
    have full : outcomes.size = count := by simpa using pending.size
    have settled : Result.settle (parallelSlots codec count outcomes) = .completed
        (match outcomes.mapM id with
          | .ok values => .success (Json.arr (values.map codec.encode))
          | .error error => .failure error) := by
      rw [← full, parallelSlots_full, settle_encoded]
      cases outcomes.mapM id <;> rfl
    have recorded := group.recorded
    rw [settled] at recorded
    have parentRoute := route.preserve group.completed group.ancestors
    cases selected : outcomes.mapM id with
    | ok values =>
      rw [selected] at recorded
      refine ⟨{
        location := start.next, finalJournal := group.finalJournal, cost := group.cost + 1, nextSteps := steps + 1
        nonempty := Location.next_nonempty _ nonempty
        sameDepth := Location.size_next _, sameParent := Location.next_parent_eq _
        ready := ⟨group.fresh, parentRoute.advance_parallel law values recorded⟩
        completed := group.completed, ancestors := group.ancestors
        correct := ?_
      }⟩
      intro fuel positive
      have reduced := walk_recorded_parallel blobs root fuel codec law count branches continuation values start start
        group.finalJournal finalWorld (by simp [Location.entersChild]) recorded
      have driven := driveWalk_reduce (α := β) blobs (fuel + 1) fuel root _ _ start start start.next start
        group.finalJournal group.finalJournal finalWorld finalWorld (by omega) reduced
      rw [driveWalk_frontier blobs fuel root _ start.next start (Location.next_nonempty start nonempty)
        (Location.next_not_before nonempty (by simp [Location.before]))] at driven
      have combined := (group.correct (fuel + 1) (by omega)).trans driven
      simpa only [controlRemainder, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined
    | error error =>
      rw [selected] at recorded
      refine ⟨{
        location := start, finalJournal := group.finalJournal, cost := group.cost, nextSteps := 0
        nonempty := nonempty, sameDepth := rfl, sameParent := rfl
        ready := .failure error recorded group.fresh
        completed := group.completed, ancestors := group.ancestors
        correct := ?_
      }⟩
      intro fuel positive
      obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      have reduced := walk_recorded_parallel_failure blobs root fuel codec count branches continuation error start start
        group.finalJournal finalWorld (by simp [Location.entersChild]) recorded
      have driven := driveWalk_reduce (α := β) blobs (fuel + 1) (fuel + 1) root _ _ start start start start
        group.finalJournal group.finalJournal finalWorld finalWorld (by omega) reduced
      rw [driveWalk_failure] at driven
      exact (group.correct (fuel + 1) (by omega)).trans driven

end LeanCloud.Proofs
