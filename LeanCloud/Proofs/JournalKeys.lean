import LeanCloud.JournalDb
import Init.Data.Nat.ToString
import Init.Data.List.SplitOn.Lemmas

/-! Physical fields cannot alias, even across different logical locations. -/

namespace LeanCloud.Proofs.JournalLayout
open Lean JournalDb

private def lastComponent (key : String) : Option (List Char) :=
  (key.toList.splitOn '/').getLast?

private theorem last_component_append (key suffix : String) (separated : '/' ∉ suffix.toList) :
    lastComponent (key ++ "/" ++ suffix) = some suffix.toList := by
  simp only [lastComponent, String.toList_append, show "/".toList = ['/'] from rfl, List.append_assoc]
  simp only [List.singleton_append, List.splitOn_append_cons_self,
    List.splitOn_eq_singleton separated, List.getLast?_append, List.getLast?_singleton, Option.some_or]

private theorem digits_no_separator (n : Nat) : '/' ∉ (toString n).toList := by
  intro member
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10)
    (by simpa using member : _ ∈ Nat.toDigits 10 _)
  contradiction

private theorem result_component (key : String) : lastComponent (resultKey key) = some "result".toList := by
  simpa only [resultKey, String.append_assoc, show "/" ++ "result" = "/result" from rfl] using
    last_component_append key "result" (by decide)

private theorem fork_component (key : String) : lastComponent (forkKey key) = some "fork".toList := by
  simpa only [forkKey, String.append_assoc, show "/" ++ "fork" = "/fork" from rfl] using
    last_component_append key "fork" (by decide)

private theorem child_component (key : String) (index : Nat) :
    lastComponent (childKey key index) = some (toString index).toList := by
  simpa only [childKey, String.append_assoc, show "/child" ++ "/" = "/child/" from rfl] using
    last_component_append (key ++ "/child") (toString index) (digits_no_separator index)

/-- Result caches and fork descriptors are distinct across all logical keys. -/
theorem result_ne_fork (left right : String) : resultKey left ≠ forkKey right := by
  intro equal
  have := congrArg lastComponent equal
  rw [result_component, fork_component] at this
  contradiction

private theorem word_ne_digits (word : String) (letter : Char) (member : letter ∈ word.toList)
    (notDigit : letter.isDigit = false) (index : Nat) : word.toList ≠ (toString index).toList := by
  intro same
  rw [same] at member
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10)
    (by simpa using member : _ ∈ Nat.toDigits 10 _)
  simp [notDigit] at digit

theorem result_ne_child (left right : String) (index : Nat) : resultKey left ≠ childKey right index := by
  intro equal
  have := congrArg lastComponent equal
  rw [result_component, child_component] at this
  exact word_ne_digits "result" 'r' (by decide) (by decide) index (Option.some.inj this)

theorem fork_ne_child (left right : String) (index : Nat) : forkKey left ≠ childKey right index := by
  intro equal
  have := congrArg lastComponent equal
  rw [fork_component, child_component] at this
  exact word_ne_digits "fork" 'f' (by decide) (by decide) index (Option.some.inj this)

theorem result_key_injective {left right : String} (equal : resultKey left = resultKey right) : left = right :=
  (String.append_left_inj "/result").mp equal

theorem fork_key_injective {left right : String} (equal : forkKey left = forkKey right) : left = right :=
  (String.append_left_inj "/fork").mp equal

/-- A child field identifies both its logical parent and array position. -/
theorem child_key_injective {left right : String} {i j : Nat}
    (equal : childKey left i = childKey right j) : left = right ∧ i = j := by
  have digits := congrArg lastComponent equal
  rw [child_component, child_component] at digits
  have decoded := congrArg (fun text : List Char => Nat.ofDigitChars 10 text 0) (Option.some.inj digits)
  have same : i = j := by simpa using decoded
  subst j
  exact ⟨(String.append_left_inj "/child/").mp
    ((String.append_left_inj (toString i)).mp equal), rfl⟩

end LeanCloud.Proofs.JournalLayout
