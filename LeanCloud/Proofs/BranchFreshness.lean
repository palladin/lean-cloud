import LeanCloud.Proofs.Freshness

/-! Freshness within a branch's remaining region. The upper endpoint is the
following sibling's first location, used only in the proof. -/

namespace LeanCloud.Proofs.Journal
open Lean

/-- All locations in the half-open interval `[start, stop)` are unrecorded.
Lexicographic location order is only used to describe regions, not scheduling. -/
def FreshBetween (journal : Journal) (start stop : Location) : Prop :=
  ∀ location : Location, 0 < location.size →
    ¬location.Earlier start → location.Earlier stop → journal location.key = none

theorem FreshBetween.empty (start stop : Location) : FreshBetween empty start stop :=
  fun _ _ _ _ => rfl

theorem FreshBetween.missing {journal : Journal} {start stop : Location}
    (fresh : FreshBetween journal start stop) (nonempty : 0 < start.size)
    (inside : start.Earlier stop) : journal start.key = none :=
  fresh start nonempty (Location.Earlier.irrefl start) inside

theorem FreshBetween.advance {journal : Journal} {start next stop : Location}
    (fresh : FreshBetween journal start stop) (later : start.Earlier next) :
    FreshBetween journal next stop :=
  fun location nonempty notEarlier beforeStop =>
    fresh location nonempty (fun earlier => notEarlier (earlier.trans later)) beforeStop

theorem FreshBetween.narrow {journal : Journal} {start stop nearer : Location}
    (fresh : FreshBetween journal start stop) (earlier : nearer.Earlier stop) :
    FreshBetween journal start nearer :=
  fun location nonempty notEarlier beforeStop =>
    fresh location nonempty notEarlier (beforeStop.trans earlier)

theorem FreshBetween.write_before {journal : Journal} {start stop written : Location}
    (fresh : FreshBetween journal start stop) (nonempty : 0 < written.size)
    (earlier : written.Earlier start) (value : Json) :
    FreshBetween (journal.write written.key value) start stop := by
  intro location locationNonempty notEarlier beforeStop
  rw [read_write_other]
  · exact fresh location locationNonempty notEarlier beforeStop
  · intro sameKey
    have equal := Location.key_injective locationNonempty nonempty sameKey
    subst location
    exact notEarlier earlier

/-- Recording a sequential result consumes only the selected branch's current
command. The remainder of this branch stays fresh. -/
theorem FreshBetween.next {journal : Journal} {start stop : Location}
    (fresh : FreshBetween journal start stop) (nonempty : 0 < start.size) (value : Json) :
    FreshBetween (journal.write start.key value) start.next stop := by
  have later := Location.earlier_next start nonempty
  exact (fresh.advance later).write_before nonempty later value

/-- Forking yields a fresh region for every child, with its following sibling
as the exclusive upper endpoint. Children may then advance in any order. -/
theorem FreshBetween.child {journal : Journal} {start stop : Location}
    (fresh : FreshBetween journal start stop) (nonempty : 0 < start.size)
    (index : Nat) (inside : (start.child (index + 1)).Earlier stop) (value : Json) :
    FreshBetween (journal.write start.key value) (start.child index) (start.child (index + 1)) := by
  have later := Location.earlier_child start index
  exact ((fresh.advance later).narrow inside).write_before nonempty later value

end LeanCloud.Proofs.Journal
