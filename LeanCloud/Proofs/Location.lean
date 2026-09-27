import LeanCloud.Location
import Init.Data.Nat.ToString
import Init.Data.String.Lemmas.Intercalate
import Init.Data.List.SplitOn.Lemmas
import Init.Data.Array.Extract
import Init.Omega

/-! Navigation and unambiguous storage keys for nonempty replay locations.
The decoder below is only a proof device; the runtime key format is unchanged. -/

namespace LeanCloud.Location

private def levelKey (position : Nat × Nat) : String := s!"{position.1}:{position.2}"

private theorem separator_not_in_digits (separator : Char) (notDigit : separator.isDigit = false)
    (n : Nat) : separator ∉ Nat.toDigits 10 n := by
  intro member
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) member
  simp [notDigit] at digit

private theorem level_no_separator (position : Nat × Nat) : '/' ∉ (levelKey position).toList := by
  simp [levelKey, String.toList_append, show (toString ":").toList = [':'] from rfl,
    separator_not_in_digits '/' (by decide)]

private def decodeLevel (chars : List Char) : Nat × Nat :=
  match chars.splitOn ':' with
  | [branch, command] => (Nat.ofDigitChars 10 branch 0, Nat.ofDigitChars 10 command 0)
  | _ => (0, 0)

private theorem decodeLevel_key (position : Nat × Nat) :
    decodeLevel (levelKey position).toList = position := by
  have split : (levelKey position).toList.splitOn ':' =
      [Nat.toDigits 10 position.1, Nat.toDigits 10 position.2] := by
    have separated := List.splitOn_intercalate ':'
      (ls := [Nat.toDigits 10 position.1, Nat.toDigits 10 position.2])
      (by simp [separator_not_in_digits ':' (by decide)]) (by simp)
    simpa [levelKey, String.toList_append, List.intercalate,
      show (toString ":").toList = [':'] from rfl] using separated
  simp [decodeLevel, split]

private def decodeKey (text : String) : List (Nat × Nat) :=
  (text.toList.splitOn '/').map decodeLevel

private theorem decodeKey_key (location : Location) (nonempty : 0 < location.size) :
    decodeKey location.key = location.toList := by
  have separated := List.splitOn_intercalate '/'
    (ls := location.toList.map fun position => (levelKey position).toList)
    (by simp only [List.mem_map]; rintro _ ⟨position, _, rfl⟩; exact level_no_separator position)
    (by simpa using (Nat.ne_of_gt nonempty))
  have split : location.key.toList.splitOn '/' =
      location.toList.map (fun position => (levelKey position).toList) := by
    simpa only [key, levelKey, String.toList_intercalate, List.map_map, Function.comp_def,
      show "/".toList = ['/'] from rfl] using separated
  simp only [decodeKey, split, List.map_map, Function.comp_def, decodeLevel_key]
  change location.toList.map id = location.toList
  exact List.map_id _

/-- Distinct nonempty locations cannot alias the same journal key. Every location
used by the interpreter is nonempty, beginning with the root position. -/
theorem key_injective {left right : Location} (leftNonempty : 0 < left.size)
    (rightNonempty : 0 < right.size) (equal : left.key = right.key) : left = right := by
  have decoded := congrArg decodeKey equal
  rw [decodeKey_key left leftNonempty, decodeKey_key right rightNonempty] at decoded
  exact Array.toList_inj.mp decoded

@[simp] theorem size_root : root.size = 1 := rfl

@[simp] theorem size_child (location : Location) (index : Nat) :
    (location.child index).size = location.size + 1 := by simp [child]

@[simp] theorem size_next (location : Location) : location.next.size = location.size := by
  simp [next]

theorem child_nonempty (location : Location) (index : Nat) :
    0 < (location.child index).size := by simp

theorem next_nonempty (location : Location) (nonempty : 0 < location.size) :
    0 < location.next.size := by simpa using nonempty

theorem parent_child (location : Location) (nonempty : 0 < location.size) (index : Nat) :
    (location.child index).parent? = some (location, index) := by
  simp [parent?, child, show ¬location.size + 1 ≤ 1 by omega]

theorem enters_child (location : Location) (index : Nat) :
    location.entersChild (location.child index) = true := by
  simp [entersChild, child]

theorem child_injective {left right : Location} {i j : Nat}
    (equal : left.child i = right.child j) : left = right ∧ i = j := by
  have parts := Array.push_eq_push.mp equal
  exact ⟨parts.2, congrArg Prod.fst parts.1⟩

theorem next_command (location : Location) (nonempty : 0 < location.size) :
    location.next[location.size - 1]!.2 = location[location.size - 1]!.2 + 1 := by
  unfold next
  rw [Array.getElem!_set!_self _ _ _ (by omega)]

theorem before_next (location : Location) (nonempty : 0 < location.size) :
    location.before location.next = true := by
  simp [before, next_command location nonempty]

theorem next_ne (location : Location) (nonempty : 0 < location.size) : location.next ≠ location := by
  intro equal
  have changed := next_command location nonempty
  rw [equal] at changed
  omega

theorem next_key_ne (location : Location) (nonempty : 0 < location.size) :
    location.next.key ≠ location.key := by
  intro equal
  exact next_ne location nonempty (key_injective (next_nonempty location nonempty) nonempty equal)

theorem child_keys_distinct (location : Location) {i j : Nat} (different : i ≠ j) :
    (location.child i).key ≠ (location.child j).key := by
  intro equal
  exact different (child_injective (key_injective (child_nonempty location i)
    (child_nonempty location j) equal)).2

/-- A child's current command may have advanced since entry; its parent still
has exactly one fewer location level. -/
theorem parent_size {current parent : Location} {index : Nat}
    (hasParent : current.parent? = some (parent, index)) :
    0 < parent.size ∧ current.size = parent.size + 1 := by
  unfold parent? at hasParent
  split at hasParent
  · cases hasParent
  · have equal := (Option.some.inj hasParent).symm
    have parentEqual := congrArg Prod.fst equal
    simp only at parentEqual
    rw [parentEqual]
    simp only [Array.size_extract]
    omega

theorem parent_key_ne {current parent : Location} {index : Nat}
    (hasParent : current.parent? = some (parent, index)) : parent.key ≠ current.key := by
  obtain ⟨nonempty, size⟩ := parent_size hasParent
  intro equal
  have same := key_injective nonempty (by omega) equal
  have sameSize := congrArg Array.size same
  omega

theorem entersChild_size {current target : Location}
    (enters : current.entersChild target = true) : current.size < target.size := by
  simp only [entersChild, Bool.and_eq_true, decide_eq_true_eq] at enters
  exact enters.1

/-- At each depth, a target has only one ancestor location. -/
theorem entersChild_unique {left right target : Location}
    (size : left.size = right.size)
    (leftEnters : left.entersChild target = true)
    (rightEnters : right.entersChild target = true) : left = right := by
  simp only [entersChild, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at leftEnters rightEnters
  rw [size] at leftEnters
  exact leftEnters.2.trans rightEnters.2.symm

/-- A completed group earlier in the branch cannot be an ancestor of the
requested location: the ancestor fork has a later command index. -/
theorem earlier_not_enters {current endpoint target : Location}
    (size : current.size = endpoint.size)
    (earlier : current[current.size - 1]!.2 < endpoint[endpoint.size - 1]!.2)
    (aligned : endpoint = target ∨ endpoint.entersChild target = true) :
    current.entersChild target = false := by
  rcases aligned with rfl | enters
  · simp [entersChild, size]
  · cases currentEnters : current.entersChild target with
    | false => rfl
    | true =>
      have equal := entersChild_unique size currentEnters enters
      subst current
      omega

theorem next_root_branch (location : Location) (nonempty : 0 < location.size) :
    location.next[0]!.1 = location[0]!.1 := by
  by_cases singleton : location.size = 1
  · simp [next, singleton]
  · unfold next
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]

theorem child_root_branch (location : Location) (nonempty : 0 < location.size) (index : Nat) :
    (location.child index)[0]!.1 = location[0]!.1 := by
  simp [child, nonempty, Array.getElem_push_lt nonempty]

theorem next_branch (location : Location) (index : Nat) (inside : index < location.size) :
    location.next[index]!.1 = location[index]!.1 := by
  unfold next
  by_cases last : location.size - 1 = index
  · rw [last, Array.getElem!_set!_self _ _ _ inside]
  · rw [Array.getElem!_set!_ne _ _ _ _ last]

theorem next_extract (location : Location) (count : Nat) (shallower : count < location.size) :
    location.next.extract 0 count = location.extract 0 count := by
  simp only [next, Array.set!, Array.setIfInBounds,
    show location.size - 1 < location.size by omega, ↓reduceDIte]
  rw [Array.extract_set]
  simp [show ¬location.size - 1 < min count location.size by omega]

/-- Advancing the command in a child leaves its ancestor forks unchanged. -/
theorem entersChild_next {ancestor target : Location}
    (enters : ancestor.entersChild target = true) : ancestor.entersChild target.next = true := by
  have depth := entersChild_size enters
  simpa only [entersChild, size_next, next_extract target ancestor.size depth] using enters

/-- Descending one more level retains every existing ancestor fork. -/
theorem entersChild_child {ancestor target : Location}
    (enters : ancestor.entersChild target = true) (index : Nat) :
    ancestor.entersChild (target.child index) = true := by
  have depth := entersChild_size enters
  simp only [entersChild, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at enters ⊢
  constructor
  · simp only [size_child]; omega
  · simpa only [child, Array.extract_push_of_le (Nat.le_of_lt depth)] using enters.2

theorem child_branch (location : Location) (index childIndex : Nat) (inside : index < location.size) :
    (location.child childIndex)[index]!.1 = location[index]!.1 := by
  have pushedInside : index < (location.push (childIndex, 0)).size := by
    simp only [Array.size_push]; omega
  simp only [child, getElem!_pos (location.push (childIndex, 0)) index pushedInside,
    getElem!_pos location index inside, Array.getElem_push_lt inside]

end LeanCloud.Location
