import LeanCloud.Proofs.Location

namespace LeanCloud.Proofs.Routing
open LeanCloud

/-- The destination retains the source's ancestry and branch number, and its
command at that depth is no earlier. It may also descend into further children. -/
structure Follows (source target : Location) : Prop where
  nonempty : 0 < source.size
  depth : source.size ≤ target.size
  ancestry : ∀ index, index + 1 < source.size → source[index]! = target[index]!
  branch : source[source.size - 1]!.1 = target[source.size - 1]!.1
  command : source[source.size - 1]!.2 ≤ target[source.size - 1]!.2

theorem Follows.refl (location : Location) (nonempty : 0 < location.size) : Follows location location :=
  ⟨nonempty, Nat.le_refl _, fun _ _ => rfl, rfl, Nat.le_refl _⟩

theorem Follows.trans {first middle last : Location} (a : Follows first middle) (b : Follows middle last) :
    Follows first last := by
  refine ⟨a.nonempty, Nat.le_trans a.depth b.depth, ?_, ?_, ?_⟩
  · intro index inside
    exact (a.ancestry index inside).trans (b.ancestry index (by have := a.depth; omega))
  · by_cases same : first.size = middle.size
    · exact a.branch.trans (by simpa only [same] using b.branch)
    · rw [← b.ancestry (first.size - 1) (by have := a.nonempty; have := a.depth; omega)]
      exact a.branch
  · by_cases same : first.size = middle.size
    · exact Nat.le_trans a.command (by simpa only [same] using b.command)
    · rw [← b.ancestry (first.size - 1) (by have := a.nonempty; have := a.depth; omega)]
      exact a.command

theorem Follows.antisymm {first last : Location} (a : Follows first last) (b : Follows last first) : first = last := by
  have sizes := Nat.le_antisymm a.depth b.depth
  apply Array.ext sizes
  intro index inside₁ inside₂
  have pair : first[index]! = last[index]! := by
    by_cases earlier : index + 1 < first.size
    · exact a.ancestry index earlier
    · have atLast : index = first.size - 1 := by omega
      subst index
      apply Prod.ext a.branch
      exact Nat.le_antisymm a.command (by simpa only [sizes] using b.command)
  simpa only [getElem!_pos first index inside₁, getElem!_pos last index inside₂] using pair

theorem Follows.branch_at {source target : Location} (follows : Follows source target)
    (index : Nat) (inside : index < source.size) : source[index]!.1 = target[index]!.1 := by
  by_cases earlier : index + 1 < source.size
  · exact congrArg Prod.fst (follows.ancestry index earlier)
  · have atLast : index = source.size - 1 := by omega
    simpa only [atLast] using follows.branch

theorem Follows.same_branch {source target : Location} (follows : Follows source target)
    (depth : source.size = target.size) :
    Proofs.Location.branchStart source = Proofs.Location.branchStart target := by
  apply Array.ext (by simp [depth])
  intro index left right
  have inside : index < source.size := by simpa using left
  by_cases last : index = source.size - 1
  · subst index
    simp [Proofs.Location.branchStart, Array.set!, ← depth, follows.branch]
  · have earlier : index + 1 < source.size := by omega
    have same := follows.ancestry index earlier
    simpa [Proofs.Location.branchStart, Array.set!, Array.getElem_setIfInBounds inside,
      Array.getElem_setIfInBounds (show index < target.size by omega), ← depth, Ne.symm last,
      getElem!_pos source index inside, getElem!_pos target index (by omega)] using same

private theorem at_push (location : Location) (address : Nat × Nat) (index : Nat) (inside : index < location.size) :
    (location.push address)[index]! = location[index]! := by
  rw [getElem!_pos _ index (by simp; omega), getElem!_pos _ index inside, Array.getElem_push_lt inside]

theorem next_follows (location : Location) (nonempty : 0 < location.size) : Follows location location.next := by
  obtain ⟨parent, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_size_pos nonempty
  rw [Location.next_push]
  refine ⟨by simp, by simp, ?_, ?_, ?_⟩
  · intro index inside
    have bound : index < parent.size := by simpa using inside
    rw [at_push _ _ _ bound, at_push _ _ _ bound]
  · simp
  · simp

theorem next_ne (location : Location) (nonempty : 0 < location.size) : location ≠ location.next := by
  obtain ⟨parent, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_size_pos nonempty
  simp [Location.next_push, Array.push_inj_right]

theorem skip_next (location : Location) : location.entersChild location.next = false := by
  simp [LeanCloud.Location.entersChild, LeanCloud.Location.next]

theorem child_follows (location : Location) (nonempty : 0 < location.size) (child : Nat) :
    Follows location (location.child child) := by
  refine ⟨nonempty, by simp [LeanCloud.Location.child], ?_, ?_, ?_⟩
  · intro index inside
    have bound : index < location.size := by omega
    simp only [LeanCloud.Location.child, at_push _ _ _ bound]
  · have bound : location.size - 1 < location.size := by omega
    simp only [LeanCloud.Location.child, at_push _ _ _ bound]
  · have bound : location.size - 1 < location.size := by omega
    simp only [LeanCloud.Location.child, at_push _ _ _ bound, Nat.le_refl]

private theorem at_extract (source target : Location) (depth : source.size ≤ target.size)
    (index : Nat) (inside : index < source.size) : (target.extract 0 source.size)[index]! = target[index]! := by
  rw [getElem!_pos (target.extract 0 source.size) index (by simpa [Nat.min_eq_left depth] using inside),
    Array.getElem_extract]
  simp only [Nat.zero_add, getElem!_pos target index (Nat.lt_of_lt_of_le inside depth)]

theorem entersChild_iff (source target : Location) :
    source.entersChild target = true ↔ source.size < target.size ∧
      ∀ index, index < source.size → source[index]! = target[index]! := by
  simp only [LeanCloud.Location.entersChild, Bool.and_eq_true_iff, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨depth, same⟩
    refine ⟨depth, ?_⟩
    intro index inside
    exact (congrArg (fun location : Location => location[index]!) same).trans
      (at_extract source target (Nat.le_of_lt depth) index inside)
  · rintro ⟨depth, entries⟩
    refine ⟨depth, ?_⟩
    apply Array.ext (by simp [Nat.min_eq_left (Nat.le_of_lt depth)])
    intro index inside₁ inside₂
    have same := (entries index inside₁).trans (at_extract source target (Nat.le_of_lt depth) index inside₁).symm
    simpa only [getElem!_pos source index inside₁, getElem!_pos (target.extract 0 source.size) index inside₂] using same

theorem enters_child (location : Location) (child : Nat) : location.entersChild (location.child child) = true := by
  apply (entersChild_iff _ _).mpr
  exact ⟨by simp [LeanCloud.Location.child], fun index inside => (at_push location (child, 0) index inside).symm⟩

theorem enters_branchStart {source target : Location} (depth : source.size < target.size) :
    source.entersChild (Proofs.Location.branchStart target) = source.entersChild target := by
  apply Bool.eq_iff_iff.mpr
  simp only [entersChild_iff, Proofs.Location.branchStart_size, depth, true_and]
  constructor <;> intro entries index inside
  · simpa only [Proofs.Location.branchStart_ancestor target index (by omega)] using entries index inside
  · simpa only [Proofs.Location.branchStart_ancestor target index (by omega)] using entries index inside

/-- Extending a destination retains all earlier ancestor decisions. -/
theorem enters_follows {source middle target : Location} (enters : source.entersChild middle = true)
    (later : Follows middle target) : source.entersChild target = true := by
  obtain ⟨depth, entries⟩ := (entersChild_iff source middle).mp enters
  apply (entersChild_iff source target).mpr
  refine ⟨Nat.lt_of_lt_of_le depth later.depth, ?_⟩
  intro index inside
  exact (entries index inside).trans (later.ancestry index (by omega))

/-- A destination extended along its branch cannot turn a previously skipped
group into a selected ancestor, unless that group was the old destination. -/
theorem skip_follows {source middle target : Location} (earlier : Follows source middle)
    (later : Follows middle target) (different : source ≠ middle)
    (skip : source.entersChild middle = false) : source.entersChild target = false := by
  apply Bool.eq_false_iff.mpr
  intro enters
  obtain ⟨depth, entries⟩ := (entersChild_iff source target).mp enters
  by_cases sameDepth : source.size = middle.size
  · have backwards : Follows middle source := by
      refine ⟨later.nonempty, Nat.le_of_eq sameDepth.symm, ?_, ?_, ?_⟩
      · intro index inside
        exact (earlier.ancestry index (by omega)).symm
      · simpa only [sameDepth] using earlier.branch.symm
      · have atLast := entries (source.size - 1) (by have := earlier.nonempty; omega)
        have bounded := later.command
        rw [← sameDepth, ← atLast] at bounded
        simpa only [sameDepth] using bounded
    exact different (earlier.antisymm backwards)
  · have depthMiddle : source.size < middle.size := by have := earlier.depth; omega
    have oldEnters : source.entersChild middle = true := by
      apply (entersChild_iff source middle).mpr
      refine ⟨depthMiddle, ?_⟩
      intro index inside
      exact (entries index inside).trans (later.ancestry index (by omega)).symm
    simp [skip] at oldEnters

end LeanCloud.Proofs.Routing
