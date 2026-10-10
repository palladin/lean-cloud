import LeanCloud.Proofs.Location
import LeanCloud.Proofs.ReplayModel

/-! Disjoint regions of the location tree let us assemble the pure workflow's
expected records. These are proof predicates, not runtime data structures. -/

namespace LeanCloud.Proofs.JournalRegion
open ReplayModel

/-- Either kind of replay record at one location. -/
def At (location : LeanCloud.Location) (key : String) : Prop :=
  key = ReplayStore.valueKey location ∨ key = ReplayStore.returnKey location

theorem At.unique {left right key} (first : At left key) (second : At right key) : left = right := by
  rcases first with first | first <;> rcases second with second | second
  · exact Location.value_key_injective (first.symm.trans second)
  · exact False.elim (Location.value_key_ne_return_key left right (first.symm.trans second))
  · exact False.elim (Location.value_key_ne_return_key right left (second.symm.trans first))
  · exact Location.return_key_injective (first.symm.trans second)

/-- All commands and descendants of one child branch. -/
def Under (parent : LeanCloud.Location) (branch : Nat) (key : String) : Prop :=
  ∃ command tail, At (parent.push (branch, command) ++ tail) key

theorem Under.separate {parent left right key} (different : left ≠ right)
    (first : Under parent left key) (second : Under parent right key) : False := by
  obtain ⟨_, _, first⟩ := first
  obtain ⟨_, _, second⟩ := second
  have same := Array.append_inj_left (first.unique second) (by simp)
  exact different (congrArg Prod.fst (Array.push_inj_right.mp same))

theorem Under.not_parent {parent branch key} (inside : Under parent branch key)
    (atParent : At parent key) : False := by
  obtain ⟨_, _, found⟩ := inside
  have sizes := congrArg Array.size (found.unique atParent)
  simp only [Array.size_append, Array.size_push] at sizes
  omega

/-- A branch suffix includes its own intermediate values and all descendant
records. Its own completion record is added only when the branch is assembled. -/
def After (parent : LeanCloud.Location) (branch command : Nat) (key : String) : Prop :=
  ∃ index tail, command ≤ index ∧
    (key = ReplayStore.valueKey (parent.push (branch, index) ++ tail) ∨
      (tail ≠ #[] ∧ key = ReplayStore.returnKey (parent.push (branch, index) ++ tail)))

def Covers (region : String → Prop) (journal : Journal) : Prop :=
  ∀ entry ∈ journal, region entry.1

theorem After.under {parent branch command key} (inside : After parent branch command key) :
    Under parent branch key := by
  obtain ⟨index, tail, _, first | ⟨_, second⟩⟩ := inside
  · exact ⟨index, tail, .inl first⟩
  · exact ⟨index, tail, .inr second⟩

theorem After.weaken {parent branch command later key} (bound : command ≤ later)
    (inside : After parent branch later key) : After parent branch command key := by
  obtain ⟨index, tail, bound', found⟩ := inside
  exact ⟨index, tail, Nat.le_trans bound bound', found⟩

theorem After.value (parent : LeanCloud.Location) (branch command : Nat) :
    After parent branch command (ReplayStore.valueKey (parent.push (branch, command))) :=
  ⟨command, #[], Nat.le_refl _, .inl (by simp)⟩

theorem After.child {parent branch command child key}
    (inside : Under (parent.push (branch, command)) child key) : After parent branch command key := by
  obtain ⟨index, tail, first | second⟩ := inside
  · exact ⟨command, #[(child, index)] ++ tail, Nat.le_refl _, .inl (by simpa using first)⟩
  · refine ⟨command, #[(child, index)] ++ tail, Nat.le_refl _, .inr ⟨?_, ?_⟩⟩
    · intro empty
      have := congrArg Array.size empty
      simp at this
    · simpa using second

/-- All writes owned by a branch, including its descendants. -/
def Owns (branch : LeanCloud.Location) (key : String) : Prop :=
  ∀ parent index, branch = parent.child index → Under parent index key

theorem Owns.returned (branch : LeanCloud.Location) : Owns branch (ReplayStore.returnKey branch) := by
  intro parent index same
  exact ⟨0, #[], .inr (by simp [same, LeanCloud.Location.child])⟩

private theorem current_shape {current parent : LeanCloud.Location} {index : Nat}
    (same : Location.branchStart current = parent.child index) :
    ∃ command, current = parent.push (index, command) := by
  by_cases empty : current = #[]
  · subst current
    have sizes := congrArg Array.size same
    simp [LeanCloud.Location.child] at sizes
  · obtain ⟨ancestry, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_ne_empty empty
    simp only [Location.branchStart_push, LeanCloud.Location.child, Array.push_eq_push, Prod.mk.injEq, and_true] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨command, rfl⟩

theorem Owns.value {branch current : LeanCloud.Location}
    (same : branch = Location.branchStart current) : Owns branch (ReplayStore.valueKey current) := by
  intro parent index eq
  obtain ⟨command, rfl⟩ := current_shape (same.symm.trans eq)
  exact ⟨command, #[], .inl (by simp)⟩

theorem Owns.child {branch current : LeanCloud.Location} {index : Nat} {key : String}
    (same : branch = Location.branchStart current) (inside : Owns (current.child index) key) :
    Owns branch key := by
  intro parent branchIndex eq
  obtain ⟨command, shape⟩ := current_shape (same.symm.trans eq)
  have region := inside current index rfl
  rw [shape] at region
  exact (After.child region).under

theorem After.not_earlier {parent branch command earlier key tail}
    (bound : earlier < command) (inside : After parent branch command key)
    (old : At (parent.push (branch, earlier) ++ tail) key) : False := by
  obtain ⟨index, suffix, lower, found⟩ := inside
  have located : At (parent.push (branch, index) ++ suffix) key :=
    found.elim Or.inl (fun returned => .inr returned.2)
  have same := Array.append_inj_left (old.unique located) (by simp)
  have equalCommands := congrArg Prod.snd (Array.push_inj_right.mp same)
  omega

theorem After.not_return {parent branch command start}
    (inside : After parent branch command (ReplayStore.returnKey (parent.push (branch, start)))) : False := by
  obtain ⟨index, tail, _, value | ⟨nonempty, returned⟩⟩ := inside
  · exact Location.value_key_ne_return_key _ _ value.symm
  · have same := Location.return_key_injective returned
    have sizes := congrArg Array.size same
    simp only [Array.size_push, Array.size_append] at sizes
    exact nonempty (Array.eq_empty_of_size_eq_zero (by omega))

theorem Covers.return_absent {parent branch command start journal}
    (covered : Covers (After parent branch command) journal) :
    journal.lookup (ReplayStore.returnKey (parent.push (branch, start))) = none := by
  apply List.lookup_eq_none_iff.mpr
  intro entry member
  apply bne_iff_ne.mpr
  intro same
  exact After.not_return (same ▸ covered entry member)

theorem Covers.add_return {parent branch command start journal}
    (covered : Covers (After parent branch command) journal) (record : ReplayRecord) :
    let after := (ReplayStore.returnKey (parent.push (branch, start)), record) :: journal
    Extends journal after ∧ Covers (Under parent branch) after := by
  have absent := covered.return_absent (start := start)
  constructor
  · simpa [store, StateT.run, absent] using
      create_extends journal (ReplayStore.returnKey (parent.push (branch, start))) record
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨start, #[], .inr (by simp)⟩
    · exact (covered entry member).under

/-- Put one command before its descendants and continuation. None of the three
parts can hide a record from another part. -/
theorem assemble (parent : LeanCloud.Location) (branch command : Nat)
    (children rest : Journal) (record : ReplayRecord)
    (childRegion : Covers (fun key => ∃ child, Under (parent.push (branch, command)) child key) children)
    (restRegion : Covers (After parent branch (command + 1)) rest) :
    let current := parent.push (branch, command)
    let all := (ReplayStore.valueKey current, record) :: (children ++ rest)
    Extends children all ∧ Extends rest all ∧
      all.lookup (ReplayStore.valueKey current) = some record ∧
      Covers (After parent branch command) all := by
  have missing : (children ++ rest).lookup (ReplayStore.valueKey (parent.push (branch, command))) = none := by
    apply List.lookup_eq_none_iff.mpr
    intro entry member
    apply bne_iff_ne.mpr
    intro same
    rcases List.mem_append.mp member with member | member
    · obtain ⟨child, inside⟩ := childRegion entry member
      exact inside.not_parent (.inl same.symm)
    · exact After.not_earlier (tail := #[]) (Nat.lt_succ_self command) (restRegion entry member)
        (.inl (by simpa using same.symm))
  have prefixExtension : Extends (children ++ rest)
      ((ReplayStore.valueKey (parent.push (branch, command)), record) :: (children ++ rest)) := by
    simpa [store, StateT.run, missing] using
      create_extends (children ++ rest) (ReplayStore.valueKey (parent.push (branch, command))) record
  refine ⟨(Extends.append_left children rest).trans prefixExtension, ?_, by simp, ?_⟩
  · apply (Extends.append_right children rest ?_).trans prefixExtension
    intro entry member other found same
    obtain ⟨child, index, tail, located⟩ := childRegion entry member
    apply After.not_earlier (earlier := command) (tail := #[(child, index)] ++ tail)
      (Nat.lt_succ_self command) (restRegion other found)
    simpa [← same] using located
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact After.value parent branch command
    · rcases List.mem_append.mp member with member | member
      · obtain ⟨_, inside⟩ := childRegion entry member
        exact After.child inside
      · exact (restRegion entry member).weaken (Nat.le_succ _)

end LeanCloud.Proofs.JournalRegion
