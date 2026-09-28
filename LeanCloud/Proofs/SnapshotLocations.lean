import LeanCloud.Proofs.ReplaySnapshot

/-! Pending work stays inside its original branch. A completion can update the
branch's enclosing group, but no unrelated branch's journal region. -/

namespace LeanCloud.Proofs
open Lean

def InBranch (parent : Location) (branch : Nat) (location : Location) : Prop :=
  (parent.child branch = location ∨ (parent.child branch).Earlier location) ∧
    location.Earlier (parent.child (branch + 1))

theorem command_in_branch (parent : Location) (branch command : Nat) :
    InBranch parent branch (commandLocation parent branch command) := by
  constructor
  · simpa only [Array.append_empty, commandLocation] using Location.child_before_extension parent branch command #[]
  · exact Location.child_earlier_sibling parent branch command (branch + 1) (by omega)

private theorem InBranch.between_parent {parent location : Location} {branch : Nat}
    (inside : InBranch parent branch location) (nonempty : 0 < parent.size) :
    parent.Earlier location ∧ location.Earlier parent.next := by
  constructor
  · rcases inside.1 with same | later
    · exact same ▸ Location.earlier_child parent branch
    · exact (Location.earlier_child parent branch).trans later
  · apply inside.2.trans
    simpa only [Location.child, Array.push_eq_append] using
      Location.descendants_earlier_next parent #[(branch + 1, 0)] nonempty

private theorem between_command_in_branch {parent location : Location} {branch command : Nat}
    (later : (commandLocation parent branch command).Earlier location)
    (earlier : location.Earlier (commandLocation parent branch command).next) :
    InBranch parent branch location := by
  constructor
  · right
    rcases (command_in_branch parent branch command).1 with same | before
    · exact same ▸ later
    · exact before.trans later
  · apply earlier.trans
    simpa only [commandLocation, Location.next_push] using
      Location.child_earlier_sibling parent branch (command + 1) (branch + 1) (by omega)

mutual
  theorem ReplaySnapshot.locations {journal : Journal} {program : Cloud Id Json}
      {parent branch command status pending target}
      (snapshot : ReplaySnapshot journal program parent branch command status pending)
      (selected : target ∈ pending) :
      InBranch parent branch target ∧
        ∀ ancestor index, target.parent? = some (ancestor, index) →
          ancestor = parent ∨ InBranch parent branch ancestor := by
    match snapshot with
    | .pending .. =>
      have same : target = commandLocation parent branch command := by simpa using selected
      subst target
      refine ⟨command_in_branch parent branch command, ?_⟩
      intro ancestor index linked
      obtain ⟨last, shape⟩ := Location.shape_of_parent linked
      exact .inl (Array.push_eq_push.mp shape).2.symm
    | .returned .. | .failed .. | .parallelFailure .. => cases selected
    | .delay rest | .parallelSuccess _ _ _ rest => exact rest.locations selected
    | .parallel (outcomes := outcomes) children _ _ =>
      cases collected : outcomes.mapM id with
      | some values =>
        have same : target = commandLocation parent branch command := by
          simpa only [groupPending, collected, List.mem_singleton] using selected
        subst target
        refine ⟨command_in_branch parent branch command, ?_⟩
        intro ancestor index linked
        obtain ⟨last, shape⟩ := Location.shape_of_parent linked
        exact .inl (Array.push_eq_push.mp shape).2.symm
      | none =>
        simp only [groupPending, collected] at selected
        obtain ⟨later, earlier, parents⟩ := children.locations (by simp [commandLocation]) selected
        refine ⟨between_command_in_branch later earlier, ?_⟩
        intro ancestor index linked
        rcases parents ancestor index linked with same | within
        · exact .inr (same ▸ command_in_branch parent branch command)
        · exact .inr (between_command_in_branch within.1 within.2)
  termination_by structural snapshot

  theorem ChildSnapshots.locations {journal : Journal} {codec : Codec α} {count : Nat}
      {branches : Fin count → Cloud Id α} {parent offset outcomes pending target}
      (snapshot : ChildSnapshots journal codec branches parent offset outcomes pending)
      (nonempty : 0 < parent.size) (selected : target ∈ pending) :
      parent.Earlier target ∧ target.Earlier parent.next ∧
        ∀ ancestor index, target.parent? = some (ancestor, index) →
          ancestor = parent ∨ (parent.Earlier ancestor ∧ ancestor.Earlier parent.next) := by
    match snapshot with
    | .empty .. => cases selected
    | .cons head tail =>
      rcases List.mem_append.mp selected with first | later
      · obtain ⟨inside, parents⟩ := head.locations first
        obtain ⟨afterParent, beforeNext⟩ := inside.between_parent nonempty
        refine ⟨afterParent, beforeNext, ?_⟩
        intro ancestor index linked
        rcases parents ancestor index linked with same | within
        · exact .inl same
        · exact .inr (within.between_parent nonempty)
      · exact tail.locations nonempty later
  termination_by structural snapshot
end

/-- A pending location is at or after the first command of its snapshot. -/
theorem ReplaySnapshot.at_or_after {journal : Journal} {program : Cloud Id Json}
    {parent branch command status pending target}
    (snapshot : ReplaySnapshot journal program parent branch command status pending)
    (selected : target ∈ pending) :
    commandLocation parent branch command = target ∨ (commandLocation parent branch command).Earlier target := by
  match snapshot with
  | .pending .. => exact .inl (List.mem_singleton.mp selected).symm
  | .returned .. | .failed .. | .parallelFailure .. => cases selected
  | .delay rest => exact rest.at_or_after selected
  | .parallelSuccess _ _ _ rest =>
    have before := Location.command_earlier parent branch command (command + 1) (by omega)
    rcases rest.at_or_after selected with same | later
    · exact .inr (same ▸ before)
    · exact .inr (before.trans later)
  | .parallel (outcomes := outcomes) children _ _ =>
    cases collected : outcomes.mapM id with
    | some _ =>
      apply Or.inl
      have same : target = commandLocation parent branch command := by simpa only [groupPending, collected, List.mem_singleton] using selected
      exact same.symm
    | none =>
      simp only [groupPending, collected] at selected
      exact .inr (children.locations (by simp [commandLocation]) selected).1
termination_by structural snapshot

end LeanCloud.Proofs
