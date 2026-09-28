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

@[simp] theorem size_child (location : Location) (index : Nat) :
    (location.child index).size = location.size + 1 := by simp [child]

@[simp] theorem size_next (location : Location) : location.next.size = location.size := by
  simp [next]

theorem parent_child (location : Location) (nonempty : 0 < location.size) (index : Nat) :
    (location.child index).parent? = some (location, index) := by
  simp [parent?, child, show ¬location.size + 1 ≤ 1 by omega]

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

/-- Every position of an ancestor is preserved in a descendant's location. -/
theorem entersChild_position {ancestor target : Location}
    (enters : ancestor.entersChild target = true) (index : Nat)
    (inside : index < ancestor.size) : target[index]! = ancestor[index]! := by
  simp only [entersChild, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at enters
  have same := congrArg (fun location : Location => location[index]!) enters.2
  simpa [getElem!_pos, inside, show index < target.size by omega,
    show index < min ancestor.size target.size by omega] using same.symm

/-- Descending through nested groups retains the outer ancestor. -/
theorem entersChild_trans {ancestor middle target : Location}
    (first : ancestor.entersChild middle = true) (second : middle.entersChild target = true) :
    ancestor.entersChild target = true := by
  simp only [entersChild, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at first second ⊢
  refine ⟨by omega, ?_⟩
  have same := congrArg (fun location : Location => location.extract 0 ancestor.size) second.2
  simp only [Array.extract_extract, Nat.zero_add, Nat.min_eq_left (Nat.le_of_lt first.1)] at same
  exact first.2.trans same

end LeanCloud.Location
