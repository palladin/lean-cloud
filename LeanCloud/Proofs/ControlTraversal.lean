import LeanCloud.Proofs.GroupTraversal

/-! One control request reduces to its continuation or reports its failure.
Every transition below is a segment of the current queue-driven interpreter. -/

namespace LeanCloud.Proofs.ReplayModel
open Lean LeanEff ReplayInterpreter.Internal

private theorem collect_list_length (outcomes : List (Except CloudError α)) (values : List α)
    (collected : outcomes.mapM id = .ok values) : values.length = outcomes.length := by
  induction outcomes generalizing values with
  | nil => change Except.ok [] = Except.ok values at collected; cases collected; rfl
  | cons head tail ih =>
    cases head with
    | error error => simp [List.mapM_cons, bind, Except.bind] at collected
    | ok value =>
      simp only [List.mapM_cons] at collected
      cases selected : tail.mapM id with
      | error error => simp [selected, bind, Except.bind] at collected
      | ok rest =>
        simp [selected, bind, Except.bind, pure, Except.pure] at collected
        subst values
        simp [ih rest selected]

private theorem collect_size (outcomes : Array (Except CloudError α)) (values : Array α)
    (collected : outcomes.mapM id = .ok values) : values.size = outcomes.size := by
  simp only [Array.mapM_eq_mapM_toList] at collected
  cases selected : outcomes.toList.mapM id with
  | error error => simp [selected, Functor.map, Except.map] at collected
  | ok rest =>
    simp [selected, Functor.map, Except.map] at collected
    subst values
    simpa using collect_list_length outcomes.toList rest selected

theorem walk_join_parallel (blobs : BlobModel World) (fuel : Nat)
    (codec : Codec α) (law : CodecLaw codec) (count : Nat)
    (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json) (values : Array α)
    (current : Location) (state : State) (world : World)
    (size : values.size = count)
    (recorded : state.journal current.key =
      some (toJson (Result.completed (.success (Json.arr (values.map codec.encode)))))) :
    (walk (storage blobs) (fuel + 1) (.impure (.parallel codec count branches) continuation) current current).run state world =
      ((.ok (.runnable #[current.next]), state), world) := by
  rw [walk]
  simp only [run_bind, load_recorded blobs state world current _ recorded, beq_self_eq_true,
    Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    ← size, decode_group_encoded codec law values, run_pure]

structure ControlTraversal {World α : Type} (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (request : Control (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) α Json) (start : Location)
    (journal : Journal) (world : World) (outcome : Except CloudError α) (finalWorld : World) where
  location : Location
  finalJournal : Journal
  nextSteps : Nat
  nonempty : 0 < location.size
  sameDepth : location.size = start.size
  sameParent : location.parent? = start.parent?
  ready : match outcome with
    | .ok value => finalJournal.Fresh location ∧
      ReplayRoute finalJournal root Location.root (ArrsF.apply continuation value) location nextSteps
    | .error error => ReturnReady finalJournal location (.failure error)
  completed : journal.PreservesCompleted finalJournal
  ancestors : journal.PreservesAncestors finalJournal start
  correct : ∀ (parent : Parent) (rest : List Location), parent.Valid start journal →
    match outcome with
    | .ok _ => Segment blobs root ⟨journal, start :: rest, none⟩ world
        ⟨finalJournal, location :: rest, none⟩ finalWorld
    | .error error => Segment blobs root ⟨journal, start :: rest, none⟩ world
        (parent.after finalJournal location (.failure error) rest) finalWorld

theorem ControlEvaluation.traverse {World α : Type} {blobs : BlobModel World}
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
    Nonempty (ControlTraversal blobs root request continuation start journal world outcome finalWorld) := by
  have nonempty : 0 < start.size := by have := route.depth_le; simp only [Location.size_root] at this; omega
  cases execution with
  | delay world =>
    exact ⟨{
      location := start, finalJournal := journal, nextSteps := steps + 1
      nonempty := nonempty, sameDepth := rfl, sameParent := rfl
      ready := ⟨fresh, route.advance_delay⟩
      completed := .refl _, ancestors := .refl _ _
      correct := fun _ _ _ => .refl _ _
    }⟩
  | fail world error =>
    let failed := BranchTraversal.of_failure (blobs := blobs) (world := world) error continuation steps route fresh
    exact ⟨{
      location := start, finalJournal := journal, nextSteps := 0
      nonempty := nonempty, sameDepth := rfl, sameParent := rfl
      ready := .fresh fresh, completed := .refl _, ancestors := .refl _ _
      correct := failed.correct
    }⟩
  | @sequential α codec operation world finalWorld outcome law executed =>
    cases outcome with
    | ok value =>
      refine ⟨{
        location := start.next
        finalJournal := journal.write start.key (toJson (Result.completed (.success (codec.encode value))))
        nextSteps := steps + 1
        nonempty := Location.next_nonempty _ nonempty
        sameDepth := Location.size_next _, sameParent := Location.next_parent_eq _
        ready := ⟨fresh.next nonempty _, route.advance_sequential law value (fresh.missing nonempty)⟩
        completed := journal.preservesCompleted_write_missing _ _ (fresh.missing nonempty)
        ancestors := journal.write_preserves_shallower _ _ _ nonempty (by omega)
        correct := ?_
      }⟩
      intro parent rest valid
      have advanced : Segment blobs root ⟨journal, start :: rest, none⟩ world
          (update ⟨journal.write start.key (toJson (Result.completed (.success (codec.encode value)))), start :: rest, none⟩
            start (.runnable #[start.next])) finalWorld := by
        apply Segment.one (bound := steps + 1)
        intro fuel enough
        rw [show fuel = (fuel - steps - 1 + 1) + steps by omega, route.from_root valid.openParent]
        apply walk_fresh_sequential blobs _ codec law operation continuation value start _ world finalWorld
          (fresh.missing nonempty)
        rw [execute, executed]
      simpa [update_head] using advanced
    | error error =>
      let failed := BranchTraversal.of_sequential_failure codec operation continuation error finalWorld steps route fresh executed
      exact ⟨{
        location := failed.location, finalJournal := failed.finalJournal, nextSteps := 0
        nonempty := failed.nonempty, sameDepth := failed.sameDepth, sameParent := failed.sameParent
        ready := failed.ready, completed := failed.completed, ancestors := failed.ancestors
        correct := failed.correct
      }⟩
  | @parallel α codec count branches world finalWorld outcomes childWork law children =>
    have pending := ChildrenEvaluation.pending codec children smaller (by omega) branches 0 (by omega)
      (by intro index; simp only [Nat.zero_add])
    obtain ⟨group⟩ := pending.start route fresh
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
      have size : values.size = count := (collect_size outcomes values selected).trans full
      refine ⟨{
        location := start.next, finalJournal := group.finalJournal, nextSteps := steps + 1
        nonempty := Location.next_nonempty _ nonempty
        sameDepth := Location.size_next _, sameParent := Location.next_parent_eq _
        ready := ⟨group.fresh, parentRoute.advance_parallel law values size recorded⟩
        completed := group.completed, ancestors := group.ancestors
        correct := ?_
      }⟩
      intro parent rest valid
      have joined : Segment blobs root ⟨group.finalJournal, start :: rest, none⟩ finalWorld
          (update ⟨group.finalJournal, start :: rest, none⟩ start (.runnable #[start.next])) finalWorld := by
        apply Segment.one (bound := steps + 1)
        intro fuel enough
        rw [show fuel = (fuel - steps - 1 + 1) + steps by omega,
          parentRoute.from_root (valid.preserve rfl group.ancestors).openParent]
        exact walk_join_parallel blobs _ codec law count branches continuation values start _ finalWorld size recorded
      exact (group.correct parent rest valid).trans (by
        simpa [update_head] using joined)
    | error error =>
      rw [selected] at recorded
      refine ⟨{
        location := start, finalJournal := group.finalJournal, nextSteps := 0
        nonempty := nonempty, sameDepth := rfl, sameParent := rfl
        ready := .failure error recorded group.fresh
        completed := group.completed, ancestors := group.ancestors
        correct := ?_
      }⟩
      intro parent rest valid
      exact (group.correct parent rest valid).trans
        (report_segment blobs root _ parent start (.failure error) group.finalJournal finalWorld rest steps
          parentRoute (.failure error recorded group.fresh) (valid.preserve rfl group.ancestors)
          (fun fuel => walk_recorded_parallel_failure blobs fuel codec count branches continuation error start _ finalWorld recorded))

end LeanCloud.Proofs.ReplayModel
