import LeanCloud.JournalDb
import LeanCloud.Proofs.JournalKeys
import LeanCloud.Proofs.Db

/-! Isolation laws for the physical journal keys over the ideal atomic map.
These establish independent sibling writes and protection from late fork
initialization, not a refinement proof for the whole adapter or interpreter. -/

namespace LeanCloud.Proofs
open Lean JournalDb

theorem Journal.write_commute (journal : Journal) (left right : String)
    (first second : Json) (different : left ≠ right) :
    (journal.write left first).write right second =
      (journal.write right second).write left first := by
  funext queried
  by_cases a : queried = left <;> by_cases b : queried = right <;>
    simp_all [Journal.write]

namespace JournalLayout

theorem childKey_injective (key : String) {left right : Nat}
    (equal : childKey key left = childKey key right) : left = right :=
  (child_key_injective equal).2

theorem resultKey_ne_forkKey (key : String) : resultKey key ≠ forkKey key := result_ne_fork key key

/-- Sibling workers can publish their outcomes in either order. -/
theorem sibling_writes_commute (journal : Journal) (key : String)
    (left right : Nat) (first second : Exit) (different : left ≠ right) :
    (journal.write (childKey key left) (toJson first)).write (childKey key right) (toJson second) =
      (journal.write (childKey key right) (toJson second)).write (childKey key left) (toJson first) := by
  apply journal.write_commute
  exact fun equal => different (childKey_injective key equal)

/-- Publishing a sibling leaves an already recorded child outcome intact. -/
theorem sibling_write_preserves (journal : Journal) (key : String)
    (left right : Nat) (outcome : Exit) (different : left ≠ right) :
    journal.write (childKey key right) (toJson outcome) (childKey key left) =
      journal (childKey key left) := by
  apply journal.read_write_other
  exact fun equal => different (childKey_injective key equal)

/-- A delayed fork initializer cannot overwrite a completed group's record. -/
theorem fork_write_preserves_result (journal : Journal) (key : String) (count : Nat) :
    journal.write (forkKey key) (toJson count) (resultKey key) = journal (resultKey key) := by
  exact journal.read_write_other _ _ _ (resultKey_ne_forkKey key)

end JournalLayout
end LeanCloud.Proofs
