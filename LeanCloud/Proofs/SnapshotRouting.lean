import LeanCloud.Proofs.ReplaySnapshot
import LeanCloud.Proofs.ReplayCompletion

/-! Pending snapshot locations retain their branch and an open parent. These
facts justify the worker's location guards and its descent into parallel groups. -/

namespace LeanCloud.Proofs
open Lean ReplayModel

theorem commandLocation_next (parent : Location) (branch command : Nat) :
    (commandLocation parent branch command).next = commandLocation parent branch (command + 1) :=
  Location.next_push parent branch command

private theorem parent_open_next {journal : Journal} {parent : Location} {branch command : Nat}
    (opened : ParentOpen journal (commandLocation parent branch command)) :
    ParentOpen journal (commandLocation parent branch (command + 1)) := by
  intro ancestor index linked
  rw [← commandLocation_next, Location.next_parent_eq] at linked
  exact opened ancestor index linked

private theorem parent_open_child {journal : Journal} {parent : Location}
    (nonempty : 0 < parent.size)
    (recorded : ∃ children, journal parent.key = some (toJson (Result.suspended children)))
    (index : Nat) : ParentOpen journal (commandLocation parent index 0) := by
  intro ancestor child linked
  change (parent.child index).parent? = some (ancestor, child) at linked
  rw [Location.parent_child parent nonempty index] at linked
  cases linked
  exact recorded

mutual
  theorem ReplaySnapshot.pending_path {journal : Journal} {program : Cloud Id Json}
      {parent branch command status pending target}
      (snapshot : ReplaySnapshot journal program parent branch command status pending)
      (opened : ParentOpen journal (commandLocation parent branch command))
      (selected : target ∈ pending) :
      parent.entersChild target = true ∧ target[parent.size]!.1 = branch ∧ ParentOpen journal target := by
    match snapshot with
    | .pending .. =>
      have same : target = commandLocation parent branch command := by simpa using selected
      subst target
      exact ⟨by simp [commandLocation, Location.entersChild], by simp [commandLocation], opened⟩
    | .returned .. | .failed .. | .parallelFailure .. => cases selected
    | .delay rest => exact rest.pending_path opened selected
    | .parallelSuccess _ _ _ rest => exact rest.pending_path (parent_open_next opened) selected
    | .parallel (outcomes := outcomes) children recorded _ =>
      cases collected : outcomes.mapM id with
      | some values =>
        have same : target = commandLocation parent branch command := by
          simpa only [groupPending, collected, List.mem_singleton] using selected
        subst target
        exact ⟨by simp [commandLocation, Location.entersChild], by simp [commandLocation], opened⟩
      | none =>
        simp only [groupPending, collected] at selected
        rw [outcomeSlots_waits _ _ collected] at recorded
        obtain ⟨enters, targetOpen⟩ := children.pending_path (by simp [commandLocation]) ⟨_, recorded⟩ selected
        refine ⟨Location.entersChild_trans (by simp [commandLocation, Location.entersChild]) enters, ?_, targetOpen⟩
        have position := Location.entersChild_position enters parent.size (by simp [commandLocation])
        simpa [commandLocation] using congrArg Prod.fst position
  termination_by structural snapshot

  theorem ChildSnapshots.pending_path {journal : Journal} {codec : Codec α} {count : Nat}
      {branches : Fin count → Cloud Id α} {parent offset outcomes pending target}
      (snapshot : ChildSnapshots journal codec branches parent offset outcomes pending)
      (nonempty : 0 < parent.size)
      (recorded : ∃ children, journal parent.key = some (toJson (Result.suspended children)))
      (selected : target ∈ pending) :
      parent.entersChild target = true ∧ ParentOpen journal target := by
    match snapshot with
    | .empty .. => cases selected
    | .cons head tail =>
      rcases List.mem_append.mp selected with first | later
      · obtain ⟨enters, _, targetOpen⟩ := head.pending_path (parent_open_child nonempty recorded _) first
        exact ⟨enters, targetOpen⟩
      · exact tail.pending_path nonempty recorded later
  termination_by structural snapshot
end

end LeanCloud.Proofs
