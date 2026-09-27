import LeanCloud.Proofs.Model
import LeanCloud.Proofs.Location
import LeanCloud.Proofs.Codecs

/-! Journal laws for the ideal storage model, including isolation of the actual
string keys used for distinct replay locations. -/

namespace LeanCloud.Proofs.Journal
open Lean

@[simp] theorem read_empty (key : String) : empty key = none := rfl

@[simp] theorem read_write (journal : Journal) (key : String) (value : Json) :
    journal.write key value key = some value := by simp [write]

theorem read_write_other (journal : Journal) (key other : String) (value : Json)
    (different : other ≠ key) : journal.write key value other = journal other := by
  simp [write, different]

theorem write_overwrite (journal : Journal) (key : String) (first last : Json) :
    (journal.write key first).write key last = journal.write key last := by
  funext queried
  by_cases same : queried = key <;> simp [write, same]

theorem write_existing (journal : Journal) (key : String) (value : Json)
    (recorded : journal key = some value) : journal.write key value = journal := by
  funext queried
  by_cases same : queried = key
  · subst queried; simp [recorded]
  · exact read_write_other _ _ _ _ same

/-- Updates to distinct keys commute in the ideal map model. This algebraic fact
does not assert atomicity for a concurrent database implementation. -/
theorem write_commute (journal : Journal) (left right : String) (a b : Json)
    (different : left ≠ right) :
    (journal.write left a).write right b = (journal.write right b).write left a := by
  funext queried
  by_cases isLeft : queried = left
  · subst queried; simp [write, different]
  · simp [write, isLeft]

/-- Storing one reachable location cannot overwrite another location's record. -/
theorem write_preserves_other_location (journal : Journal) (left right : Location) (value : Json)
    (leftNonempty : 0 < left.size) (rightNonempty : 0 < right.size) (different : left ≠ right) :
    journal.write left.key value right.key = journal right.key := by
  apply read_write_other
  intro equal
  exact different (Location.key_injective leftNonempty rightNonempty equal.symm)

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

/-- A journal update leaves the records at strictly shallower locations intact. -/
def PreservesAncestors (before after : Journal) (target : Location) : Prop :=
  ∀ location : Location, 0 < location.size → location.size < target.size →
    after location.key = before location.key

theorem PreservesAncestors.refl (journal : Journal) (target : Location) :
    PreservesAncestors journal journal target := fun _ _ _ => rfl

theorem PreservesAncestors.trans {first second third : Journal} {target : Location}
    (left : PreservesAncestors first second target) (right : PreservesAncestors second third target) :
    PreservesAncestors first third target := by
  intro location nonempty shallower
  exact (right location nonempty shallower).trans (left location nonempty shallower)

theorem PreservesAncestors.of_depth_le {before after : Journal} {first second : Location}
    (preserved : PreservesAncestors before after second) (depth : first.size ≤ second.size) :
    PreservesAncestors before after first :=
  fun location nonempty shallower => preserved location nonempty (by omega)

theorem write_preserves_shallower (journal : Journal) (written start : Location) (value : Json)
    (nonempty : 0 < written.size) (depth : start.size ≤ written.size) :
    PreservesAncestors journal (journal.write written.key value) start := by
  intro location locationNonempty shallower
  apply read_write_other
  intro equalKeys
  have equal := Location.key_injective locationNonempty nonempty equalKeys
  subst location
  omega

end LeanCloud.Proofs.Journal
