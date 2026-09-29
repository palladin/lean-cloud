import LeanCloud.Proofs.Model
import LeanCloud.Proofs.Location
import LeanCloud.Proofs.Codecs

/-! Journal laws for the ideal Db model, including isolation of the actual
string keys used for distinct replay locations. -/

namespace LeanCloud.Proofs.Journal
open Lean

@[simp] theorem read_write (journal : Journal) (key : String) (value : Json) :
    journal.write key value key = some value := by simp [write]

theorem read_write_other (journal : Journal) (key other : String) (value : Json)
    (different : other ≠ key) : journal.write key value other = journal other := by
  simp [write, different]

theorem write_existing (journal : Journal) (key : String) (value : Json)
    (recorded : journal key = some value) : journal.write key value = journal := by
  funext queried
  by_cases same : queried = key
  · subst queried; simp [recorded]
  · exact read_write_other _ _ _ _ same

@[simp] theorem write_write (journal : Journal) (key : String) (first last : Json) :
    (journal.write key first).write key last = journal.write key last := by
  funext queried
  by_cases same : queried = key <;> simp [write, same]

/-- Every previously completed result is still recorded with the same outcome.
Partial groups may change as more children complete. -/
def PreservesCompleted (before after : Journal) : Prop :=
  ∀ key outcome, before key = some (toJson (Result.completed outcome)) →
    after key = some (toJson (Result.completed outcome))

theorem PreservesCompleted.refl (journal : Journal) : PreservesCompleted journal journal :=
  fun _ _ recorded => recorded

theorem PreservesCompleted.trans {first second third : Journal}
    (left : PreservesCompleted first second) (right : PreservesCompleted second third) :
    PreservesCompleted first third := fun key outcome recorded => right key outcome (left key outcome recorded)

/-- Filling an empty location preserves all previously completed records. -/
theorem preservesCompleted_write_missing (journal : Journal) (key : String) (value : Json)
    (missing : journal key = none) : PreservesCompleted journal (journal.write key value) := by
  intro other outcome recorded
  have different : other ≠ key := by
    intro equal
    subst other
    rw [missing] at recorded
    cases recorded
  rw [read_write_other _ _ _ _ different, recorded]

/-- Updating a partial group preserves every completed record elsewhere. The
round-trip theorem rules out confusing a serialized partial group with a result. -/
theorem preservesCompleted_write_suspended (journal : Journal) (key : String)
    (children : Array (Option Exit)) (value : Json)
    (suspended : journal key = some (toJson (Result.suspended children))) :
    PreservesCompleted journal (journal.write key value) := by
  intro other outcome recorded
  have different : other ≠ key := by
    intro equal
    subst other
    have encoded := Option.some.inj (suspended.symm.trans recorded)
    have decoded := congrArg (fromJson? (α := Result)) encoded
    simp only [result_roundtrip] at decoded
    cases decoded
  rw [read_write_other _ _ _ _ different, recorded]

end LeanCloud.Proofs.Journal
