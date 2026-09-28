import LeanCloud.Proofs.Completion
import Init.Data.List.Lex

/-! Fresh journal locations. Lexicographic
order follows branch indices, then command indices at each level. It places a
group before its children and all its descendants before its next command. -/

namespace LeanCloud.Location

private def positionEarlier (left right : Nat × Nat) : Prop :=
  left.1 < right.1 ∨ left.1 = right.1 ∧ left.2 < right.2

/-- The depth-first execution order; distinct from `before`, the runtime's test
for replaying a prefix on an already selected route. -/
def Earlier (left right : Location) : Prop :=
  List.Lex positionEarlier left.toList right.toList

theorem Earlier.irrefl (location : Location) : ¬ location.Earlier location := by
  exact List.lex_irrefl (fun position => by simp [positionEarlier]) _

theorem Earlier.trans {first second third : Location}
    (left : first.Earlier second) (right : second.Earlier third) : first.Earlier third := by
  exact List.lex_trans (fun h₁ h₂ => by unfold positionEarlier at *; omega) left right

theorem Earlier.ne {left right : Location} (earlier : left.Earlier right) : left ≠ right := by
  rintro rfl
  exact Earlier.irrefl _ earlier

private theorem lex_append_common {α : Type} {relation : α → α → Prop}
    (common : List α) {left right : List α} (earlier : List.Lex relation left right) :
    List.Lex relation (common ++ left) (common ++ right) := by
  induction common with
  | nil => exact earlier
  | cons _ _ ih => exact .cons ih

theorem next_push (base : Location) (branch command : Nat) :
    next (base.push (branch, command)) = base.push (branch, command + 1) := by
  simp [next, Array.set!, Array.setIfInBounds, Array.set_push]

theorem earlier_next (location : Location) (nonempty : 0 < location.size) :
    location.Earlier location.next := by
  obtain ⟨base, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_size_pos nonempty
  rw [next_push]
  simp only [Earlier, Array.toList_push]
  apply lex_append_common base.toList
  exact .rel (Or.inr ⟨rfl, by omega⟩)

theorem earlier_child (location : Location) (index : Nat) :
    location.Earlier (location.child index) := by
  change List.Lex positionEarlier location.toList (location.push (index, 0)).toList
  rw [Array.toList_push]
  simpa using lex_append_common location.toList (List.Lex.nil (r := positionEarlier) (a := (index, 0)) (l := []))

/-- Every descendant of a command precedes the next command in that branch. -/
theorem descendants_earlier_next (location suffix : Location) (nonempty : 0 < location.size) :
    Earlier (location ++ suffix) location.next := by
  obtain ⟨base, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_size_pos nonempty
  rw [next_push]
  simp only [Earlier, Array.toList_append, Array.toList_push, List.append_assoc]
  apply lex_append_common
  exact .rel (Or.inr ⟨rfl, by omega⟩)

/-- Every descendant in one child precedes the next sibling's first command. -/
theorem descendants_earlier_sibling (parent : Location) (index command nextIndex : Nat)
    (suffix : Location) (later : index < nextIndex) :
    Earlier (parent.push (index, command) ++ suffix) (parent.child nextIndex) := by
  simp only [Earlier, child, Array.toList_push, Array.toList_append, List.append_assoc]
  apply lex_append_common parent.toList
  exact .rel (Or.inl later)

theorem command_earlier_extension (parent : Location) (branch first last : Nat)
    (suffix : Location) (later : first < last) :
    Earlier (parent.push (branch, first)) (parent.push (branch, last) ++ suffix) := by
  simp only [Earlier, Array.toList_push, Array.toList_append, List.append_assoc]
  apply lex_append_common parent.toList
  exact .rel (Or.inr ⟨rfl, later⟩)

theorem command_earlier (parent : Location) (branch first last : Nat)
    (later : first < last) :
    Earlier (parent.push (branch, first)) (parent.push (branch, last)) := by
  simpa using command_earlier_extension parent branch first last #[] later

/-- A branch starts no later than any of its commands or nested descendants. -/
theorem child_before_extension (parent : Location) (branch command : Nat) (suffix : Location) :
    parent.child branch = parent.push (branch, command) ++ suffix ∨
      Earlier (parent.child branch) (parent.push (branch, command) ++ suffix) := by
  by_cases zero : command = 0
  · subst command
    by_cases empty : suffix = #[]
    · exact Or.inl (by simp [empty, child])
    · right
      have notNil : suffix.toList ≠ [] := by simpa using empty
      obtain ⟨head, tail, elements⟩ := List.exists_cons_of_ne_nil notNil
      simp only [Earlier, child, Array.toList_push, Array.toList_append, elements,
        List.append_assoc, List.singleton_append]
      exact lex_append_common parent.toList (.cons .nil)
  · exact Or.inr (command_earlier_extension parent branch 0 command suffix (by omega))

/-- The terminal command of any child precedes the following sibling. -/
theorem child_earlier_sibling (parent : Location) (index command nextIndex : Nat)
    (later : index < nextIndex) :
    Earlier (parent.push (index, command)) (parent.child nextIndex) := by
  simpa using descendants_earlier_sibling parent index command nextIndex #[] later

theorem shape_of_parent {current parent : Location} {index : Nat}
    (hasParent : current.parent? = some (parent, index)) :
    ∃ command, current = parent.push (index, command) := by
  obtain ⟨parentNonempty, size⟩ := parent_size hasParent
  obtain ⟨base, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_size_pos (by omega : 0 < current.size)
  have baseNonempty : 0 < base.size := by simp only [Array.size_push] at size; omega
  change parent? (base.push (branch, command)) = some (parent, index) at hasParent
  simp only [parent?, Array.size_push, show ¬base.size + 1 ≤ 1 by omega, ↓reduceIte,
    Nat.add_sub_cancel, Array.extract_push_of_le (Nat.le_refl base.size), Array.extract_size] at hasParent
  have last : (base.push (branch, command))[base.size]! = (branch, command) := by simp
  rw [last] at hasParent
  have equal := Option.some.inj hasParent
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact ⟨command, rfl⟩

theorem parent_earlier {current parent : Location} {index : Nat}
    (hasParent : current.parent? = some (parent, index)) : parent.Earlier current := by
  obtain ⟨command, rfl⟩ := shape_of_parent hasParent
  simp only [Earlier, Array.toList_push]
  simpa using lex_append_common parent.toList
    (List.Lex.nil (r := positionEarlier) (a := (index, command)) (l := []))

theorem next_parent {current parent : Location} {index : Nat}
    (hasParent : current.parent? = some (parent, index)) : current.next.parent? = some (parent, index) := by
  obtain ⟨command, rfl⟩ := shape_of_parent hasParent
  rw [next_push]
  have nonempty := (parent_size hasParent).1
  simp [parent?, show ¬parent.size + 1 ≤ 1 by omega]

theorem next_parent_eq (current : Location) : current.next.parent? = current.parent? := by
  cases hasParent : current.parent? with
  | some pair =>
    rcases pair with ⟨parent, index⟩
    exact next_parent hasParent
  | none =>
    by_cases small : current.size ≤ 1
    · simp [parent?, small]
    · simp [parent?, small] at hasParent

end LeanCloud.Location
