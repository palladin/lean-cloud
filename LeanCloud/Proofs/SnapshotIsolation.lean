import LeanCloud.Proofs.SnapshotLocations
import LeanCloud.Proofs.SnapshotPreservation
import LeanCloud.Proofs.ReplayCompletion

/-! A selected step can write its own result and its immediate parent's slots.
Both writes preserve every other sibling's entire replay snapshot. -/

namespace LeanCloud.Proofs
open Lean ReplayModel

theorem InBranch.nonempty {parent location : Location} {branch : Nat}
    (inside : InBranch parent branch location) : 0 < location.size := by
  apply Classical.byContradiction
  intro empty
  have zero : location.size = 0 := by omega
  have same := Array.eq_empty_of_size_eq_zero zero
  subst location
  rcases inside.1 with equal | later
  · have size := congrArg Array.size equal
    simp at size
  · exact List.not_lex_nil later

/-- Distinct sibling regions are disjoint, even for deeply nested locations. -/
theorem InBranch.outside {parent location : Location} {branch other : Nat}
    (inside : InBranch parent branch location) (different : branch ≠ other) :
    location.Earlier (parent.child other) ∨
      location = parent.child (other + 1) ∨ (parent.child (other + 1)).Earlier location := by
  rcases Nat.lt_or_gt_of_ne different with before | after
  · left
    by_cases adjacent : branch + 1 = other
    · simpa only [adjacent] using inside.2
    · exact inside.2.trans (Location.child_earlier_sibling parent (branch + 1) 0 other (by omega))
  · right
    by_cases adjacent : other + 1 = branch
    · rw [adjacent]
      exact inside.1.imp Eq.symm id
    · right
      have before := Location.child_earlier_sibling parent (other + 1) 0 branch (by omega)
      rcases inside.1 with same | later
      · exact same ▸ before
      · exact before.trans later

theorem InBranch.disjoint {parent location : Location} {branch other : Nat}
    (left : InBranch parent branch location) (right : InBranch parent other location)
    (different : branch ≠ other) : False := by
  rcases left.outside different with before | same | later
  · rcases right.1 with atStart | afterStart
    · exact Location.Earlier.irrefl _ (atStart ▸ before)
    · exact Location.Earlier.irrefl _ (before.trans afterStart)
  · exact Location.Earlier.irrefl _ (same ▸ right.2)
  · exact Location.Earlier.irrefl _ (right.2.trans later)

namespace Journal

/-- The only potentially changed keys are the selected location and its parent.
This describes a single serialized worker step, not concurrent database writes. -/
def TouchesAt (before after : Journal) (target : Location) : Prop :=
  ∀ key, key ≠ target.key →
    (∀ parent index, target.parent? = some (parent, index) → key ≠ parent.key) →
    after key = before key

theorem TouchesAt.refl (journal : Journal) (target : Location) : TouchesAt journal journal target :=
  fun _ _ _ => rfl

theorem TouchesAt.write (journal : Journal) (target : Location) (value : Json) :
    TouchesAt journal (journal.write target.key value) target :=
  fun key different _ => journal.read_write_other target.key key value different

private theorem outside_key_ne {queried written start stop : Location}
    (queriedNonempty : 0 < queried.size) (writtenNonempty : 0 < written.size)
    (notBefore : ¬queried.Earlier start) (beforeStop : queried.Earlier stop)
    (outside : written.Earlier start ∨ written = stop ∨ stop.Earlier written) :
    queried.key ≠ written.key := by
  intro equal
  have same := Location.key_injective queriedNonempty writtenNonempty equal
  subst queried
  rcases outside with before | rfl | after
  · exact notBefore before
  · exact Location.Earlier.irrefl _ beforeStop
  · exact Location.Earlier.irrefl _ (beforeStop.trans after)

/-- Writes confined below an earlier fork cannot occupy its continuation's
future locations. -/
theorem TouchesAt.before {journal updated : Journal} {target start stop : Location}
    (touched : TouchesAt journal updated target) (nonempty : 0 < target.size)
    (earlier : target.Earlier start)
    (parents : ∀ parent index, target.parent? = some (parent, index) → parent.Earlier start) :
    AgreesBetween journal updated start stop := by
  intro queried queriedNonempty notBefore beforeStop
  apply touched queried.key
  · exact outside_key_ne queriedNonempty nonempty notBefore beforeStop (.inl earlier)
  · intro parent index linked
    exact outside_key_ne queriedNonempty (Location.parent_size linked).1 notBefore beforeStop
      (.inl (parents parent index linked))

theorem TouchesAt.sibling {journal updated : Journal} {parent target : Location} {branch other : Nat}
    (touched : TouchesAt journal updated target) (nonempty : 0 < parent.size)
    (inside : InBranch parent branch target)
    (parents : ∀ ancestor index, target.parent? = some (ancestor, index) →
      ancestor = parent ∨ InBranch parent branch ancestor)
    (different : branch ≠ other) :
    AgreesBetween journal updated (parent.child other) (parent.child (other + 1)) := by
  intro queried queriedNonempty notBefore beforeStop
  apply touched queried.key
  · exact outside_key_ne queriedNonempty inside.nonempty notBefore beforeStop (inside.outside different)
  · intro ancestor index linked
    rcases parents ancestor index linked with same | within
    · subst ancestor
      exact outside_key_ne queriedNonempty nonempty notBefore beforeStop
        (.inl (Location.earlier_child parent other))
    · exact outside_key_ne queriedNonempty within.nonempty notBefore beforeStop (within.outside different)

end Journal

theorem ReplayModel.Parent.record_touches {owner : Parent} {journal : Journal} {location : Location}
    (valid : owner.Valid location journal) (outcome : Exit) :
    journal.TouchesAt (owner.record journal location outcome) location := by
  cases owner with
  | root => exact Journal.TouchesAt.write journal location _
  | child parent index children =>
    intro key notChild notParent
    exact journal.completeChild_other location parent children index outcome key notChild
      (notParent parent index valid.1)

theorem ReplayModel.Parent.record_preserves_missing {owner : Parent} {journal : Journal} {location : Location}
    (valid : owner.Valid location journal) (outcome : Exit) (missing : journal location.key = none) :
    journal.PreservesCompleted (owner.record journal location outcome) := by
  cases owner with
  | root => exact journal.preservesCompleted_write_missing _ _ missing
  | child parent index children =>
    exact journal.completeChild_preserves location parent children index outcome valid.1 missing valid.2.1

theorem ReplayModel.Parent.record_preserves_existing {owner : Parent} {journal : Journal} {location : Location}
    (valid : owner.Valid location journal) (outcome : Exit)
    (recorded : journal location.key = some (toJson (Result.completed outcome))) :
    journal.PreservesCompleted (owner.record journal location outcome) := by
  cases owner with
  | root =>
    rw [Parent.record, journal.write_existing _ _ recorded]
    exact .refl _
  | child parent index children =>
    exact journal.completeChild_preserves_existing location parent children index outcome recorded valid.2.1

end LeanCloud.Proofs
