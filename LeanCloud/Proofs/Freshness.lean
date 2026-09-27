import LeanCloud.Proofs.Completion
import Init.Data.List.Lex

/-! Fresh journal locations in the sequential reference scheduler. Lexicographic
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

/-- The terminal command of any child precedes the following sibling. -/
theorem child_earlier_sibling (parent : Location) (index command nextIndex : Nat)
    (later : index < nextIndex) :
    Earlier (parent.push (index, command)) (parent.child nextIndex) := by
  simp only [Earlier, child, Array.toList_push]
  apply lex_append_common parent.toList
  exact .rel (Or.inl later)

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

theorem earlier_parent_next {current parent : Location} {index : Nat}
    (hasParent : current.parent? = some (parent, index)) : current.Earlier parent.next := by
  obtain ⟨command, rfl⟩ := shape_of_parent hasParent
  have nonempty := (parent_size hasParent).1
  simpa only [Array.push_eq_append] using descendants_earlier_next parent #[(index, command)] nonempty

theorem earlier_next_sibling {current parent : Location} {index : Nat}
    (hasParent : current.parent? = some (parent, index)) : current.Earlier (parent.child (index + 1)) := by
  obtain ⟨command, rfl⟩ := shape_of_parent hasParent
  exact child_earlier_sibling parent index command (index + 1) (by omega)

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

namespace LeanCloud.Proofs.Journal
open Lean

/-- All recorded locations are strictly earlier than the next fresh frontier.
Records at ancestor groups may be updated without violating this property. -/
def Fresh (journal : Journal) (frontier : Location) : Prop :=
  ∀ location : Location, 0 < location.size → ¬location.Earlier frontier → journal location.key = none

theorem Fresh.empty (frontier : Location) : Fresh Journal.empty frontier := by
  intro location nonempty notEarlier
  rfl

theorem Fresh.missing {journal : Journal} {frontier : Location}
    (fresh : Fresh journal frontier) (nonempty : 0 < frontier.size) : journal frontier.key = none :=
  fresh frontier nonempty (Location.Earlier.irrefl frontier)

theorem Fresh.advance {journal : Journal} {frontier next : Location}
    (fresh : Fresh journal frontier) (later : frontier.Earlier next) : Fresh journal next := by
  intro location nonempty notEarlier
  exact fresh location nonempty (fun earlier => notEarlier (earlier.trans later))

theorem Fresh.write_before {journal : Journal} {frontier written : Location}
    (fresh : Fresh journal frontier) (nonempty : 0 < written.size)
    (earlier : written.Earlier frontier) (value : Json) :
    Fresh (journal.write written.key value) frontier := by
  intro location locationNonempty notEarlier
  rw [read_write_other]
  · exact fresh location locationNonempty notEarlier
  · intro sameKey
    have equal := Location.key_injective locationNonempty nonempty sameKey
    subst location
    exact notEarlier earlier

theorem Fresh.next {journal : Journal} {frontier : Location}
    (fresh : Fresh journal frontier) (nonempty : 0 < frontier.size) (value : Json) :
    Fresh (journal.write frontier.key value) frontier.next := by
  have later := Location.earlier_next frontier nonempty
  exact (fresh.advance later).write_before nonempty later value

theorem Fresh.child {journal : Journal} {frontier : Location}
    (fresh : Fresh journal frontier) (nonempty : 0 < frontier.size) (index : Nat) (value : Json) :
    Fresh (journal.write frontier.key value) (frontier.child index) := by
  have later := Location.earlier_child frontier index
  exact (fresh.advance later).write_before nonempty later value

/-- Child completion changes only locations before the next frontier, whether
it is the next sibling or the parent's continuation. -/
theorem Fresh.complete_child {journal : Journal} {current parent frontier : Location} {index : Nat}
    (fresh : Fresh journal current.next) (hasParent : current.parent? = some (parent, index))
    (later : current.next.Earlier frontier) (children : Array (Option Exit)) (outcome : Exit) :
    Fresh (journal.completeChild current parent children index outcome) frontier := by
  obtain ⟨parentNonempty, size⟩ := Location.parent_size hasParent
  have ownEarlier := (Location.earlier_next current (by omega)).trans later
  exact ((fresh.advance later).write_before (by omega) ownEarlier _).write_before parentNonempty
    ((Location.parent_earlier hasParent).trans ownEarlier) _

end LeanCloud.Proofs.Journal
