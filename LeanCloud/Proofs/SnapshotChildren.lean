import LeanCloud.Proofs.SnapshotLocalStep

/-! Reassemble a parallel group's snapshot after one selected branch advances.
The other branches retain their evaluations, results, and pending work. -/

namespace LeanCloud.Proofs
open Lean

theorem ReplaySnapshot.pending_status {journal : Journal} {program : Cloud Id Json}
    {parent branch command status pending target}
    (snapshot : ReplaySnapshot journal program parent branch command status pending)
    (selected : target ∈ pending) : status = none := by
  have nonempty : pending.isEmpty = false := List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem selected)
  have empty := snapshot.pending_empty
  rw [nonempty] at empty
  cases status with
  | none => rfl
  | some value => cases empty

theorem array_cons_get (head : α) (tail : Array α) [Inhabited α] (index : Nat) (inside : index < tail.size) :
    (#[head] ++ tail)[index + 1]! = tail[index]! := by
  rw [getElem!_pos (#[head] ++ tail) (index + 1) (by simp; omega), getElem!_pos tail index inside]
  simp

/-- Encoding cannot manufacture a new branch outcome. A finished encoded
computation always corresponds to a typed result of the original branch. -/
theorem ReplaySnapshot.typed_status {journal : Journal} {codec : Codec α}
    {program : Cloud Id α} {parent branch command status pending}
    (snapshot : ReplaySnapshot journal (codec.encode <$> program) parent branch command status pending) :
    ∃ outcome : Option (Except CloudError α), status = outcome.map (Except.map codec.encode) := by
  cases status with
  | none => exact ⟨none, rfl⟩
  | some value =>
    obtain ⟨outcome, _, equal⟩ := (snapshot.evaluation rfl).map_cases program codec.encode
    exact ⟨some outcome, congrArg some equal⟩

/-- Locate the selected leaf within its immediate branch of a parallel group. -/
theorem ChildSnapshots.select {journal : Journal} {codec : Codec α} {count : Nat}
    {branches : Fin count → Cloud Id α} {parent offset outcomes pending target}
    (snapshot : ChildSnapshots journal codec branches parent offset outcomes pending)
    (selected : target ∈ pending) :
    ∃ index : Fin count, ∃ ownPending,
      ReplaySnapshot journal (codec.encode <$> branches index) parent (offset + index.val) 0 none ownPending ∧
      target ∈ ownPending := by
  match snapshot with
  | .empty .. => cases selected
  | .cons head tail =>
    rcases List.mem_append.mp selected with first | later
    · have absent := head.pending_status first
      rw [absent] at head
      exact ⟨0, _, by simpa only [Fin.val_zero, Nat.add_zero] using head, first⟩
    · obtain ⟨index, ownPending, branch, member⟩ := tail.select later
      exact ⟨index.succ, ownPending,
        by simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using branch, member⟩
termination_by structural snapshot

theorem set_cons_zero (head value : α) (tail : Array α) :
    (#[head] ++ tail).set! 0 value = #[value] ++ tail := by
  simp [Array.set!]

theorem set_cons_succ (head value : α) (tail : Array α) (index : Nat) :
    (#[head] ++ tail).set! (index + 1) value = #[head] ++ tail.set! index value := by
  simp [Array.set!]

theorem ChildSnapshots.preserve_future {journal updated : Journal} {codec : Codec α} {count : Nat}
    {branches : Fin count → Cloud Id α} {parent offset outcomes pending target stop}
    (snapshot : ChildSnapshots journal codec branches parent offset outcomes pending)
    (nonempty : 0 < parent.size) (selected : target ∈ pending)
    (touched : journal.TouchesAt updated target)
    (fresh : journal.FreshBetween parent.next stop) : updated.FreshBetween parent.next stop := by
  obtain ⟨afterParent, beforeNext, parents⟩ := snapshot.locations nonempty selected
  obtain ⟨_, _, source, member⟩ := snapshot.select selected
  apply fresh.preserve
  apply touched.before (source.locations member).1.nonempty beforeNext
  intro ancestor index linked
  rcases parents ancestor index linked with same | between
  · rw [same]
    exact Location.earlier_next parent nonempty
  · exact between.2

/-- Rebuild the enclosing parallel command once the selected branch and its
recorded parent slot have been updated. Its continuation remains fresh. -/
theorem outcomeSlots_update (codec : Codec α) (outcomes : Array (Option (Except CloudError α)))
    (index : Nat) (value : Option (Except CloudError α)) :
    outcomeSlots codec (outcomes.set! index value) =
      (outcomeSlots codec outcomes).set! index (value.map (encodeOutcome codec)) := by
  simp only [outcomeSlots, Array.set!, Array.map_setIfInBounds]

/-- The worker's parent-slot update records exactly the newly rebuilt typed
outcome array, whether the selected branch continues, succeeds, or fails. -/
theorem slot_update_recorded {journal : Journal} (codec : Codec α) (parent : Location)
    (outcomes : Array (Option (Except CloudError α))) (index : Nat)
    (inside : index < outcomes.size) (missing : outcomes[index]! = none)
    (value : Option (Except CloudError α))
    (reported : (ReplayModel.Parent.child parent index (outcomeSlots codec outcomes)).SlotUpdate journal
      (value.map (Except.map codec.encode))) :
    journal parent.key = some (toJson (Result.settle (outcomeSlots codec (outcomes.set! index value)))) := by
  rw [outcomeSlots_update]
  cases value with
  | none =>
    have valid : index < (outcomeSlots codec outcomes).size := by simpa [outcomeSlots] using inside
    have absent : (outcomeSlots codec outcomes)[index]! = none := by
      rw [getElem!_pos (outcomeSlots codec outcomes) index valid]
      simp only [outcomeSlots, Array.getElem_map]
      rw [← getElem!_pos outcomes index inside, missing]
      rfl
    have unchanged : (outcomeSlots codec outcomes).set! index none = outcomeSlots codec outcomes := by
      rw [← absent, getElem!_pos (outcomeSlots codec outcomes) index valid]
      simp [Array.set!, Array.setIfInBounds, valid]
    simp only [Option.map_none, unchanged]
    rw [Result.settle_missing _ (Array.mem_of_getElem (i := index) (h := valid) (by simpa only [getElem!_pos (outcomeSlots codec outcomes) index valid] using absent))]
    exact reported
  | some outcome =>
    cases outcome <;> simpa only [ReplayModel.Parent.SlotUpdate, Option.map_some, Except.map, encodeOutcome] using reported

/-- Work below a parallel command cannot report that command's enclosing
branch as finished. Only a later join/continuation step may do so. -/
theorem ChildSnapshots.preserve_outer_slot {journal updated : Journal} {codec : Codec α} {count : Nat}
    {branches : Fin count → Cloud Id α} {parent offset outcomes pending target}
    (snapshot : ChildSnapshots journal codec branches parent offset outcomes pending)
    (nonempty : 0 < parent.size) (selected : target ∈ pending)
    (touched : journal.TouchesAt updated target) (owner : ReplayModel.Parent)
    (valid : owner.Valid parent journal) : owner.SlotUpdate updated none := by
  obtain ⟨afterParent, _, parents⟩ := snapshot.locations nonempty selected
  obtain ⟨_, _, source, member⟩ := snapshot.select selected
  have targetNonempty := (source.locations member).1.nonempty
  cases owner with
  | root => trivial
  | child outer index slots =>
    have outerNonempty := (Location.parent_size valid.1).1
    have before := Location.parent_earlier valid.1
    have different (written : Location) (present : 0 < written.size) (later : outer.Earlier written) :
        outer.key ≠ written.key := fun same => later.ne (Location.key_injective outerNonempty present same)
    apply Eq.trans (touched outer.key (different _ targetNonempty (before.trans afterParent)) ?_) valid.2.1
    intro ancestor child linked
    apply different ancestor (Location.parent_size linked).1
    rcases parents ancestor child linked with same | between
    · exact same ▸ before
    · exact before.trans between.1

end LeanCloud.Proofs
