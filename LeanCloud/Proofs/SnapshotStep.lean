import LeanCloud.Proofs.SnapshotEmission
import LeanCloud.Proofs.SnapshotWorkPreservation

/-! One selected worker step preserves the whole program snapshot. Its response
describes exactly the replacement of pending work, up to queue ordering. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayModel ReplayInterpreter.Internal

def BranchAdvance (program : Cloud Id Json)
    (owner : Parent) (journal : Journal) (parent : Location) (branch command : Nat)
    (pending : List Location) (target : Location) (spent : Nat) : Prop :=
  ∃ updated status nextPending response bound,
    (∃ snapshot : ReplaySnapshot updated program parent branch command status nextPending,
      SnapshotWork snapshot (spent + 1)) ∧
    journal.TouchesAt updated target ∧
    journal.PreservesCompleted updated ∧ owner.SlotUpdate updated status ∧
    BranchEmission owner status pending target response nextPending ∧
    ∀ fuel queueItems,
      (walk db noBlobs (fuel + bound) program (commandLocation parent branch command) target).run
          ⟨journal, queueItems, none⟩ =
        ((.ok response, ⟨updated, queueItems, none⟩))

theorem LocalAdvance.branch {program : Cloud Id Json}
    {owner journal parent branch command spent}
    (advanced : LocalAdvance program owner journal parent branch command (spent + 1)) :
    BranchAdvance program owner journal parent branch command
      [commandLocation parent branch command] (commandLocation parent branch command) spent := by
  obtain ⟨updated, status, pending, bound, ⟨snapshot, cost⟩, touched, kept, slots, executed⟩ := advanced
  exact ⟨updated, status, pending, _, bound, ⟨snapshot, cost⟩, touched, kept, slots,
    BranchEmission.local snapshot owner, executed⟩

def ChildrenAdvance (codec : Codec α) {count : Nat}
    (branches : Fin count → Cloud Id α) (journal : Journal) (parent : Location) (offset : Nat)
    (outcomes : Array (Option (Except CloudError α))) (pending : List Location) (target : Location) (slots : Array (Option Exit)) (spent : Nat) : Prop :=
  ∃ index : Fin count, ∃ value updated nextPending response bound,
    outcomes[index.val]! = none ∧
    (∃ snapshot : ChildSnapshots updated codec branches parent offset (outcomes.set! index.val value) nextPending,
      ChildrenSnapshotWork snapshot (spent + 1)) ∧
    journal.TouchesAt updated target ∧ journal.PreservesCompleted updated ∧
    (Parent.child parent (offset + index.val) slots).SlotUpdate updated (value.map (Except.map codec.encode)) ∧
    ChildrenEmission (.child parent (offset + index.val) slots) (value.map (Except.map codec.encode))
      pending target response nextPending ∧
    parent.entersChild target = true ∧ target[parent.size]!.1 = offset + index.val ∧
    ∀ fuel queueItems,
      (walk db noBlobs (fuel + bound) (codec.encode <$> branches index)
        (commandLocation parent (offset + index.val) 0) target).run ⟨journal, queueItems, none⟩ =
          ((.ok response, ⟨updated, queueItems, none⟩))

private theorem next_target_ne {journal : Journal} {program : Cloud Id Json}
    {parent branch command status pending target}
    (snapshot : ReplaySnapshot journal program parent branch (command + 1) status pending)
    (selected : target ∈ pending) : commandLocation parent branch command ≠ target := by
  have before : (commandLocation parent branch command).Earlier (commandLocation parent branch (command + 1)) :=
    Location.command_earlier parent branch command (command + 1) (by omega)
  rcases snapshot.at_or_after selected with same | later
  · exact (same ▸ before).ne
  · exact (before.trans later).ne

mutual
  /-- Processing any selected pending location preserves the original program's
  snapshot and publishes exactly its next pending work, in arbitrary queue order. -/
  theorem SnapshotWork.advance {journal : Journal} {program : Cloud Id Json}
      {parent branch command status pending target spent}
      {snapshot : ReplaySnapshot journal program parent branch command status pending}
      (cost : SnapshotWork snapshot spent)
      (supported : PureProgram program) (owner : Parent)
      (valid : owner.Valid (commandLocation parent branch command) journal)
      (selected : target ∈ pending) :
      BranchAdvance program owner journal parent branch command pending target spent := by
    match cost with
    | .pending _ _ _ _ fresh =>
      have same : target = commandLocation parent branch command := by simpa using selected
      subst target
      exact (fresh_local_work_advance _ owner journal parent branch command supported fresh valid).branch
    | .returned .. | .failed .. | .parallelFailure .. => cases selected
    | .delay rest =>
      obtain ⟨updated, outcome, nextPending, response, bound,
        ⟨replacement, replacementCost⟩, touched, kept, slots, emission, executed⟩ :=
        rest.advance (supported.2.apply ()) owner valid selected
      refine ⟨updated, outcome, nextPending, response, bound + 1,
        ⟨_, .delay replacementCost⟩, touched, kept, slots, emission, ?_⟩
      intro fuel queueItems
      rw [← Nat.add_assoc, walk_delay]
      exact executed fuel queueItems
    | .parallelSuccess (children := childrenEvaluation) children collected recorded rest =>
      obtain ⟨updated, outcome, nextPending, response, bound,
        ⟨replacement, replacementCost⟩, touched, kept, slots, emission, executed⟩ :=
        rest.advance (supported.2.apply _) owner (Parent.Valid.next_command valid) selected
      refine ⟨updated, outcome, nextPending, response, bound + 1,
        ?_, touched, kept, slots, emission, ?_⟩
      · have combined : ∃ result, SnapshotWork (program := .impure (.parallel _ _ _) _) result _ :=
          ⟨_, .parallelSuccess children collected (kept _ _ recorded) replacementCost⟩
        simpa only [Nat.add_assoc] using combined
      · intro fuel queueItems
        rw [← Nat.add_assoc, walk_recorded_parallel _ _ supported.1.1 _ _ _ _ _ _ _
          ((collect_outcomes_size _ _ collected).trans childrenEvaluation.size) (next_target_ne rest.source selected) recorded,
          commandLocation_next]
        exact executed fuel queueItems
    | .parallel (codec := codec) (continuation := continuation) (work := childrenSpent)
        (outcomes := outcomes) children recorded fresh =>
      cases collected : outcomes.mapM id with
      | some values =>
        have same : target = commandLocation parent branch command := by
          simpa only [groupPending, collected, List.mem_singleton] using selected
        subst target
        simpa only [groupPending, collected, Nat.add_assoc, Nat.add_comm] using
          (join_local_work_advance codec supported.1.1 _ _ continuation owner journal parent branch command
            children.source children collected recorded fresh valid).branch
      | none =>
        simp only [groupPending, collected] at selected ⊢
        rw [outcomeSlots_waits codec outcomes collected] at recorded
        obtain ⟨index, value, updated, nextPending, response, bound,
          missing, ⟨replacement, replacementCost⟩, touched, kept, slots, emission, enters, chosen, executed⟩ :=
          children.advance supported.1.2 (by simp [commandLocation]) recorded
            (by simp [outcomeSlots, children.source.size]) (fun index => by
              rw [Nat.zero_add, getElem!_pos _ _ (by simp [outcomeSlots, children.source.size]),
                getElem!_pos _ _ (by rw [children.source.size]; exact index.isLt)]
              simp only [outcomeSlots, Array.getElem_map]) selected
        simp only [Nat.zero_add] at slots emission chosen executed
        have inside : index.val < outcomes.size := by rw [children.source.size]; exact index.isLt
        have newRecord := slot_update_recorded codec _ outcomes index.val inside missing value slots
        have nextFresh := children.source.preserve_future (by simp [commandLocation]) selected touched
          (by simpa only [commandLocation_next] using fresh)
        rw [commandLocation_next] at nextFresh
        have combined : ∃ result, SnapshotWork (program := .impure (.parallel codec _ _) continuation)
            result (1 + (childrenSpent + 1)) := ⟨_, .parallel replacementCost newRecord nextFresh⟩
        refine ⟨updated, none, _, response, bound + 1,
          by simpa only [Nat.add_assoc] using combined,
          touched, kept, children.source.preserve_outer_slot (by simp [commandLocation]) selected touched owner valid,
          emission.group replacement inside missing collected owner, ?_⟩
        intro fuel queueItems
        rw [← Nat.add_assoc, walk_parallel_child _ codec _ _ _ _ _ _ _
          (by simpa [outcomeSlots] using children.source.size) enters index chosen recorded]
        exact executed fuel queueItems
  termination_by structural cost

  theorem ChildrenSnapshotWork.advance {α : Type} {journal : Journal} {codec : Codec α} {count : Nat}
      {branches : Fin count → Cloud Id α} {parent offset outcomes pending target slots spent}
      {snapshot : ChildSnapshots journal codec branches parent offset outcomes pending}
      (cost : ChildrenSnapshotWork snapshot spent)
      (supported : ∀ index, PureProgram (branches index)) (nonempty : 0 < parent.size)
      (recorded : journal parent.key = some (toJson (Result.suspended slots)))
      (bound : offset + count ≤ slots.size)
      (aligned : ∀ index : Fin count,
        slots[offset + index.val]! = outcomes[index.val]!.map (encodeOutcome codec))
      (selected : target ∈ pending) :
      ChildrenAdvance codec branches journal parent offset outcomes pending target slots spent := by
    match cost with
    | .empty .. => cases selected
    | .cons (outcome := outcome) (outcomes := tailOutcomes)
        (headPending := headPending) (tailPending := tailPending) head tail =>
      rcases List.mem_append.mp selected with first | later
      · have absent := head.source.pending_status first
        have noOutcome : outcome = none := by
          cases outcome with
          | none => rfl
          | some value => cases absent
        have firstSlot : (#[outcome] ++ tailOutcomes)[0]! = outcome := by
          rw [getElem!_pos _ _ (by simp; omega)]
          simp
        have missing := aligned 0
        simp only [Fin.val_zero, Nat.add_zero] at missing
        rw [firstSlot, noOutcome] at missing
        have valid : (Parent.child parent offset slots).Valid (commandLocation parent offset 0) journal :=
          ⟨Location.parent_child parent nonempty offset, recorded, by omega, missing⟩
        obtain ⟨updated, status, nextPending, response, steps,
          ⟨replacement, replacementCost⟩, touched, kept, reported, emission, executed⟩ :=
          head.advance ((supported 0).map codec.encode) _ valid first
        obtain ⟨value, typed⟩ := replacement.typed_status
        have measured : ∃ result : ReplaySnapshot updated _ parent offset 0 status nextPending,
            SnapshotWork result _ := ⟨replacement, replacementCost⟩
        rw [typed] at measured reported emission
        obtain ⟨replacement, replacementCost⟩ := measured
        obtain ⟨keptTail, keptTailCost⟩ := tail.preserve (fun index bound => by
          obtain ⟨inside, parents⟩ := head.source.locations first
          exact touched.sibling nonempty inside parents (by omega))
        have combined : ∃ result, ChildrenSnapshotWork (branches := branches)
            (statuses := #[value] ++ tailOutcomes) result _ :=
          ⟨_, .cons replacementCost keptTailCost ⟩
        obtain ⟨enters, chosen, _⟩ := head.source.pending_path valid.openParent first
        refine ⟨0, value, updated, nextPending ++ tailPending, response, steps,
          by simpa only [Fin.val_zero, firstSlot] using noOutcome, ?_, touched, kept,
          by simpa using reported, emission.children.append _ first, enters, ?_, ?_⟩
        · simpa only [Fin.val_zero, set_cons_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined
        · simpa only [Fin.val_zero, Nat.add_zero] using chosen
        · simpa only [Fin.val_zero, Nat.add_zero] using executed
      · obtain ⟨index, value, updated, nextPending, response, steps,
          missing, ⟨replacement, replacementCost⟩, touched, kept, reported, emission, enters, chosen, executed⟩ :=
          tail.advance (fun index => supported index.succ) nonempty recorded (by omega) (fun index => by
            have eq := aligned index.succ
            have nextSlot := array_cons_get outcome tailOutcomes index.val (by rw [tail.source.size]; exact index.isLt)
            simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, nextSlot] using eq) later
        obtain ⟨sourceIndex, _, source, member⟩ := tail.source.select later
        obtain ⟨inside, parents⟩ := source.locations member
        obtain ⟨keptHead, keptHeadCost⟩ := head.preserve
          (touched.sibling nonempty inside parents (by omega))
        have combined : ∃ result, ChildrenSnapshotWork (branches := branches)
            (statuses := #[outcome] ++ (tailOutcomes.set! index.val value)) result _ :=
          ⟨_, .cons keptHeadCost replacementCost ⟩
        have notHead : target ∉ _ := fun first =>
          (head.source.locations first).1.disjoint (source.locations member).1 (by omega)
        refine ⟨index.succ, value, updated, headPending ++ nextPending, response, steps,
          ?_, ?_, touched, kept, ?_, ?_, enters, ?_, ?_⟩
        · simpa only [Fin.val_succ, array_cons_get outcome tailOutcomes index.val (by rw [tail.source.size]; exact index.isLt)] using missing
        · simpa only [Fin.val_succ, set_cons_succ, Nat.add_assoc] using combined
        · simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reported
        · simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using emission.prepend _ notHead
        · simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using chosen
        · simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using executed
  termination_by structural cost
end

/-- One actual selected step increases processed work by exactly one. -/
theorem SnapshotWork.step_preserves {journal : Journal} {root : Cloud Id Json}
    {status pending target spent}
    {snapshot : ReplaySnapshot journal root #[] 0 0 status pending}
    (cost : SnapshotWork snapshot spent)
    (supported : PureProgram root) (selected : target ∈ pending) :
    ∃ updated outcome nextPending response bound,
      (∃ replacement : ReplaySnapshot updated root #[] 0 0 outcome nextPending,
        SnapshotWork replacement (spent + 1)) ∧
      journal.TouchesAt updated target ∧
      journal.PreservesCompleted updated ∧ BranchEmission .root outcome pending target response nextPending ∧
      ∀ fuel queueItems,
        (step db noBlobs (fuel + bound) root target).run ⟨journal, queueItems, none⟩ =
          ((.ok response, ⟨updated, queueItems, none⟩)) := by
  obtain ⟨updated, outcome, nextPending, response, bound,
    replacement, touched, kept, _, emission, executed⟩ :=
    cost.advance supported .root rfl selected
  have opened : ParentOpen journal (commandLocation #[] 0 0) := by
    intro parent index linked
    cases linked
  obtain ⟨enters, rootBranch, targetOpen⟩ := snapshot.pending_path opened selected
  have nonempty : 0 < target.size := Location.entersChild_size enters
  refine ⟨updated, outcome, nextPending, response, bound,
    replacement, touched, kept, emission, ?_⟩
  intro fuel queueItems
  rw [step_eq_walk nonempty rootBranch targetOpen]
  exact executed fuel queueItems

/-- The whole-snapshot and queue-publication guarantee for the actual worker
entry point, with no restriction on which pending location was selected. -/
theorem ReplaySnapshot.step_preserves {journal : Journal} {root : Cloud Id Json}
    {status pending target}
    (snapshot : ReplaySnapshot journal root #[] 0 0 status pending)
    (supported : PureProgram root) (selected : target ∈ pending) :
    ∃ updated outcome nextPending response bound,
      ReplaySnapshot updated root #[] 0 0 outcome nextPending ∧
      journal.TouchesAt updated target ∧
      journal.PreservesCompleted updated ∧ BranchEmission .root outcome pending target response nextPending ∧
      ∀ fuel queueItems,
        (step db noBlobs (fuel + bound) root target).run ⟨journal, queueItems, none⟩ =
          ((.ok response, ⟨updated, queueItems, none⟩)) := by
  obtain ⟨spent, cost⟩ := snapshot.work_exists
  obtain ⟨updated, outcome, nextPending, response, bound, ⟨replacement, _⟩, rest⟩ :=
    cost.step_preserves supported selected
  exact ⟨updated, outcome, nextPending, response, bound, replacement, rest⟩

end LeanCloud.Proofs
