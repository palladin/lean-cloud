import LeanCloud.Proofs.PendingChildren
import Init.Data.Array.OfFn

namespace LeanCloud.Proofs.ReplayModel
open Lean LeanEff ReplayInterpreter.Internal

def childWork (parent : Location) (index count : Nat) : List Location :=
  List.ofFn fun i : Fin (count - index) => parent.child (index + i.val)

def groupWork (parent : Location) (index count : Nat) : List Location :=
  if index < count then childWork parent index count else [parent]

theorem childWork_succ (parent : Location) (index count : Nat) (inside : index < count) :
    childWork parent index count = parent.child index :: childWork parent (index + 1) count := by
  unfold childWork
  have size : count - index = (count - (index + 1)) + 1 := by omega
  rw [size, List.ofFn_succ]
  simp only [Fin.val_zero, Nat.add_zero]
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 1
  simp only [Fin.val_succ]
  omega

theorem childWork_done (parent : Location) (count : Nat) : childWork parent count count = [] := by
  simp [childWork]

theorem encoded_map (codec : Codec α) (outcome : Except CloudError α) :
    encoded (outcome.map codec.encode) = encodeOutcome codec outcome := by cases outcome <;> rfl

structure GroupTraversal {World α : Type} (blobs : BlobModel World) (root : Cloud (StateM World) Json)
    (codec : Codec α) (count : Nat) (parent : Location) (journal : Journal)
    (past outcomes : Array (Except CloudError α)) (world finalWorld : World) where
  finalJournal : Journal
  recorded : finalJournal parent.key = some (toJson (Result.settle (parallelSlots codec count (past ++ outcomes))))
  fresh : finalJournal.Fresh parent.next
  completed : journal.PreservesCompleted finalJournal
  ancestors : journal.PreservesAncestors finalJournal parent
  correct : ∀ rest, Segment blobs root ⟨journal, groupWork parent past.size count ++ rest, none⟩ world
    ⟨finalJournal, parent :: rest, none⟩ finalWorld

theorem PendingChildren.process {World α : Type} {blobs : BlobModel World} {codec : Codec α}
    {count index : Nat} {branches : Fin count → Cloud (StateM World) α} {world finalWorld : World}
    {outcomes : Array (Except CloudError α)}
    (pending : PendingChildren blobs codec branches index world outcomes finalWorld)
    {root : Cloud (StateM World) Json} {continuation : ArrsF (Control (StateM World)) (Array α) Json}
    {parent : Location} {journal : Journal} {past : Array (Except CloudError α)} {steps : Nat}
    (pastSize : past.size = index)
    (route : ReplayRoute journal root Location.root (.impure (.parallel codec count branches) continuation) parent steps)
    (recorded : journal parent.key = some (toJson (Result.settle (parallelSlots codec count past))))
    (available : if past.size < count then journal.Fresh (parent.child past.size) else journal.Fresh parent.next) :
    Nonempty (GroupTraversal blobs root codec count parent journal past outcomes world finalWorld) := by
  match pending with
  | .done world =>
    refine ⟨{
      finalJournal := journal
      recorded := by simpa using recorded
      fresh := by simpa [pastSize] using available
      completed := .refl _
      ancestors := .refl _ _
      correct := ?_
    }⟩
    intro rest
    simpa [groupWork, pastSize] using Segment.refl (blobs := blobs) (root := root) ⟨journal, parent :: rest, none⟩ world
  | @PendingChildren.next _ _ _ _ _ _ index inside world middle finalWorld outcome outcomes traverse rest =>
    have pastInside : past.size < count := by omega
    have parentNonempty : 0 < parent.size := by have := route.depth_le; simp only [Location.size_root] at this; omega
    have suspended := recorded
    rw [parallelSlots_waits codec count past pastInside] at suspended
    let slots := parallelSlots codec count past
    have slotsSize := parallelSlots_size codec count past (by omega)
    have slotMissing := parallelSlots_get_pending codec count past past.size (by omega) pastInside
    have childRoute := route.enter_child slots suspended slotsSize ⟨index, inside⟩
    have childFresh : journal.Fresh (parent.child index) := by simpa [pastSize, inside] using available
    obtain ⟨child⟩ := traverse root (parent.child index) journal (steps + 1) childRoute childFresh
    have hasParent : child.location.parent? = some (parent, past.size) := by
      rw [child.sameParent, Location.parent_child parent parentNonempty, pastSize]
    have parentRecorded : child.finalJournal parent.key = some (toJson (Result.suspended slots)) :=
      (child.ancestors parent parentNonempty (by simp [Location.size_child])).trans suspended
    have validEnd : (Parent.child parent past.size slots).Valid child.location child.finalJournal :=
      ⟨hasParent, parentRecorded, by dsimp [slots]; rw [slotsSize]; exact pastInside, slotMissing⟩
    have parentRoute := route.preserve child.completed (child.ancestors.of_depth_le (by simp [Location.size_child]))
    let committed := child.finalJournal.completeChild child.location parent slots past.size (encodeOutcome codec outcome)
    have preserved := child.ready.preserves_completed validEnd child.nonempty
    simp only [Parent.record, encoded_map] at preserved
    have kept := child.finalJournal.completeChild_preserves_ancestors child.location parent slots past.size
      (encodeOutcome codec outcome) hasParent
    have nextRoute := parentRoute.preserve preserved kept
    have nextRecorded : committed parent.key = some (toJson (Result.settle (parallelSlots codec count (past.push outcome)))) := by
      dsimp [committed, slots]
      rw [Journal.completeChild_records_parent, parallelSlots_update codec count past pastInside]
    have nextAvailable : if (past.push outcome).size < count then committed.Fresh (parent.child (past.push outcome).size)
        else committed.Fresh parent.next := by
      split
      · simpa only [Array.size_push, encoded_map] using child.ready.fresh_sibling hasParent slots
      · simpa only [encoded_map] using child.ready.fresh_parent_next hasParent slots
    obtain ⟨tail⟩ := PendingChildren.process rest (past := past.push outcome) (journal := committed)
      (by simp [pastSize]) nextRoute nextRecorded nextAvailable
    refine ⟨{
      finalJournal := tail.finalJournal
      recorded := by simpa only [Array.push_eq_append, Array.append_assoc] using tail.recorded
      fresh := tail.fresh
      completed := child.completed.trans (preserved.trans tail.completed)
      ancestors := (child.ancestors.of_depth_le (by simp [Location.size_child])).trans (kept.trans tail.ancestors)
      correct := ?_
    }⟩
    intro outside
    have validStart : (Parent.child parent past.size slots).Valid (parent.child index) journal :=
      ⟨by rw [Location.parent_child parent parentNonempty, pastSize], suspended,
        by dsimp [slots]; rw [slotsSize]; exact pastInside, slotMissing⟩
    have ranChild := child.correct (.child parent past.size slots)
      (childWork parent (index + 1) count ++ outside) validStart
    have afterChild :
        (Parent.child parent past.size slots).after child.finalJournal child.location
          (encoded (outcome.map codec.encode)) (childWork parent (index + 1) count ++ outside) =
        ⟨committed, groupWork parent (past.push outcome).size count ++ outside, none⟩ := by
      unfold Parent.after
      simp only [encoded_map, Parent.record, Parent.result, slots,
        parallelSlots_update codec count past pastInside, Array.size_push]
      by_cases more : past.size + 1 < count
      · rw [parallelSlots_waits codec count (past.push outcome) (by simpa using more)]
        have moreIndex : index + 1 < count := by omega
        simp [update, groupWork, pastSize, moreIndex, committed, slots]
      · have full : (past.push outcome).size = count := by simp only [Array.size_push]; omega
        obtain ⟨result, settled⟩ := Result.settle_all_completed ((past.push outcome).map (encodeOutcome codec))
        have complete : Result.settle (parallelSlots codec count (past.push outcome)) = .completed result := by
          rw [← full, parallelSlots_full]
          exact settled
        rw [complete]
        have last : index + 1 = count := by omega
        simp [update, groupWork, more, last, childWork_done, committed, slots]
    rw [afterChild] at ranChild
    have chain := ranChild.trans (tail.correct outside)
    simpa only [groupWork, pastSize, inside, ↓reduceIte, childWork_succ parent index count inside,
      List.cons_append] using chain
termination_by structural pending

structure ParallelCompletion {World α : Type} (blobs : BlobModel World) (root : Cloud (StateM World) Json)
    (codec : Codec α) (count : Nat) (parent : Location) (journal : Journal)
    (outcomes : Array (Except CloudError α)) (world finalWorld : World) where
  finalJournal : Journal
  recorded : finalJournal parent.key = some (toJson (Result.settle (parallelSlots codec count outcomes)))
  fresh : finalJournal.Fresh parent.next
  completed : journal.PreservesCompleted finalJournal
  ancestors : journal.PreservesAncestors finalJournal parent
  correct : ∀ (outer : Parent) rest, outer.Valid parent journal →
    Segment blobs root ⟨journal, parent :: rest, none⟩ world ⟨finalJournal, parent :: rest, none⟩ finalWorld

theorem walk_fresh_parallel (blobs : BlobModel World) (fuel : Nat) (codec : Codec α)
    (count : Nat) (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json)
    (current : Location) (state : State) (world : World) (missing : state.journal current.key = none) :
    (walk (storage blobs) (fuel + 1) (.impure (.parallel codec count branches) continuation) current current).run state world =
      ((.ok (.runnable (if count == 0 then #[current] else Array.ofFn fun i : Fin count => current.child i.val)),
        { state with journal := state.journal.write current.key (toJson (Result.settle (Array.replicate count none))) }), world) := by
  rw [walk]
  simp only [run_bind, load_missing blobs state world current missing, beq_self_eq_true,
    Option.isNone_none, Bool.and_true, ↓reduceIte, save_result, run_pure]

theorem PendingChildren.start {World α : Type} {blobs : BlobModel World} {codec : Codec α}
    {count : Nat} {branches : Fin count → Cloud (StateM World) α} {world finalWorld : World}
    {outcomes : Array (Except CloudError α)}
    (pending : PendingChildren blobs codec branches 0 world outcomes finalWorld)
    {root : Cloud (StateM World) Json} {continuation : ArrsF (Control (StateM World)) (Array α) Json}
    {parent : Location} {journal : Journal} {steps : Nat}
    (route : ReplayRoute journal root Location.root (.impure (.parallel codec count branches) continuation) parent steps)
    (fresh : journal.Fresh parent) :
    Nonempty (ParallelCompletion blobs root codec count parent journal outcomes world finalWorld) := by
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
  obtain ⟨children⟩ := pending.process (past := #[]) rfl savedRoute savedRecord available
  refine ⟨{
    finalJournal := children.finalJournal
    recorded := by simpa using children.recorded
    fresh := children.fresh
    completed := (journal.preservesCompleted_write_missing _ _ missing).trans children.completed
    ancestors := (journal.write_preserves_shallower parent parent _ nonempty (by omega)).trans children.ancestors
    correct := ?_
  }⟩
  intro outer rest valid
  let emitted := if count == 0 then #[parent] else Array.ofFn fun i : Fin count => parent.child i.val
  have emits : emitted.toList = groupWork parent 0 count := by
    cases count <;> simp [emitted, groupWork, childWork, Array.toList_ofFn]
  have creation : Segment blobs root ⟨journal, parent :: rest, none⟩ world
      (update ⟨saved, parent :: rest, none⟩ parent (.runnable emitted)) world := by
    apply Segment.one (bound := steps + 1)
    intro fuel enough
    rw [show fuel = (fuel - steps - 1 + 1) + steps by omega, route.from_root valid.openParent]
    simpa only [saved, parallelSlots_empty] using
      walk_fresh_parallel blobs (fuel - steps - 1) codec count branches continuation parent
        ⟨journal, parent :: rest, none⟩ world missing
  rw [update_head, emits] at creation
  exact creation.trans (by simpa [saved, parallelSlots_empty] using children.correct rest)

end LeanCloud.Proofs.ReplayModel
