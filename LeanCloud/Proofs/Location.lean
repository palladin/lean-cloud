import LeanCloud.ReplayStore
import Std.Data.String.ToNat
import Init.Data.String.Lemmas.Pattern.Split.Char
import Init.Data.String.Lemmas.Intercalate

namespace LeanCloud.Proofs.Location

private def label (address : Nat × Nat) : String := s!"{address.1}:{address.2}"

private theorem repr_excludes (n : Nat) (separator : Char)
    (notDigit : separator.isDigit = false) (notUnderscore : separator ≠ '_') :
    separator ∉ (Nat.repr n).toList := by
  intro member
  have allowed := (String.isNat_iff.mp (Nat.isNat_repr n)).2.1 separator member
  simp [notDigit, notUnderscore] at allowed

private theorem label_excludes_slash (address : Nat × Nat) : '/' ∉ (label address).toList := by
  simpa [label, ToString.toString, String.toList_append] using
    And.intro (repr_excludes address.1 '/' (by decide) (by decide))
      (repr_excludes address.2 '/' (by decide) (by decide))

private theorem label_nonempty (address : Nat × Nat) : label address ≠ "" := by
  simp [label]

private theorem split_label (address : Nat × Nat) :
    ((label address).split ':').toList.map (·.copy) = [Nat.repr address.1, Nat.repr address.2] := by
  have parts := String.toList_split_intercalate (c := ':') (l := [Nat.repr address.1, Nat.repr address.2])
    (by
      intro text member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact repr_excludes address.1 ':' (by decide) (by decide)
      · exact repr_excludes address.2 ':' (by decide) (by decide))
  rw [String.intercalate_cons_cons, String.intercalate_singleton] at parts
  simpa [label, ToString.toString] using! parts

private theorem label_injective (left right : Nat × Nat) (same : label left = label right) : left = right := by
  have parts := congrArg (fun text : String => (text.split ':').toList.map (·.copy)) same
  simp only [split_label, List.cons.injEq, and_true, Nat.repr_inj] at parts
  exact Prod.ext parts.1 parts.2

private theorem split_key (location : LeanCloud.Location) :
    (((location.key).split '/').toList.map (·.copy)).filter (· != "") =
      location.toList.map label := by
  have parts := String.toList_split_intercalate (c := '/') (l := location.toList.map label) (by
    intro text member
    obtain ⟨address, _, rfl⟩ := List.mem_map.mp member
    exact label_excludes_slash address)
  have noEmpty : (location.toList.map label).filter (· != "") = location.toList.map label := by
    apply List.filter_eq_self.mpr
    intro text member
    obtain ⟨address, _, rfl⟩ := List.mem_map.mp member
    simpa using label_nonempty address
  change (((String.intercalate (String.singleton '/') (location.toList.map label)).split '/').toList.map
    (·.copy)).filter (· != "") = _
  rw [parts]
  split
  · simp_all
  · exact noEmpty

/-- The human-readable `branch:command/...` encoding never aliases locations. -/
theorem key_injective {left right : LeanCloud.Location} (same : left.key = right.key) : left = right := by
  have parts := congrArg (fun text : String =>
    ((text.split '/').toList.map (·.copy)).filter (· != "")) same
  rw [split_key, split_key] at parts
  exact Array.toList_inj.mp ((List.map_inj_right label_injective).mp parts)

theorem value_key_injective {left right : LeanCloud.Location}
    (same : ReplayStore.valueKey left = ReplayStore.valueKey right) : left = right := by
  apply key_injective
  simpa [ReplayStore.valueKey] using same

theorem return_key_injective {left right : LeanCloud.Location}
    (same : ReplayStore.returnKey left = ReplayStore.returnKey right) : left = right := by
  apply key_injective
  simpa [ReplayStore.returnKey] using same

/-- An intermediate value can never overwrite any branch's completion record. -/
theorem value_key_ne_return_key (valueLocation branch : LeanCloud.Location) :
    ReplayStore.valueKey valueLocation ≠ ReplayStore.returnKey branch := by
  intro same
  have last := congrArg (fun text : String => text.toList.getLast?) same
  simp [ReplayStore.valueKey, ReplayStore.returnKey, String.toList_append] at last

/-- Advancing a command retains the complete ancestry and branch index. -/
theorem next_push (parent : LeanCloud.Location) (branch command : Nat) :
    LeanCloud.Location.next (parent.push (branch, command)) = parent.push (branch, command + 1) := by
  simp [LeanCloud.Location.next, Array.setIfInBounds, Array.set_push]

/-- Proof-only identification of the branch containing a replay command. -/
def branchStart (location : LeanCloud.Location) : LeanCloud.Location :=
  location.set! (location.size - 1) (location[location.size - 1]!.1, 0)

@[simp] theorem branchStart_push (parent : LeanCloud.Location) (branch command : Nat) :
    branchStart (parent.push (branch, command)) = parent.push (branch, 0) := by
  simp [branchStart, Array.setIfInBounds, Array.set_push]

@[simp] theorem branchStart_next (location : LeanCloud.Location) :
    branchStart location.next = branchStart location := by
  by_cases empty : location = #[]
  · subst location; rfl
  · obtain ⟨parent, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_ne_empty empty
    simp [next_push]

@[simp] theorem branchStart_child (location : LeanCloud.Location) (index : Nat) :
    branchStart (location.child index) = location.child index := by
  simp [LeanCloud.Location.child]

@[simp] theorem branchStart_root : branchStart LeanCloud.Location.root = LeanCloud.Location.root :=
  branchStart_push #[] 0 0

end LeanCloud.Proofs.Location
