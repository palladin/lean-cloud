import LeanCloud.Proofs.ReplaySnapshot

/-! Transport a snapshot across changes outside its branch. This is the frame
property needed when a different parallel child advances or completes. -/

namespace LeanCloud.Proofs
open Lean

namespace Journal

/-- Two journals agree on the half-open location region `[start, stop)`. -/
def AgreesBetween (before after : Journal) (start stop : Location) : Prop :=
  ∀ location : Location, 0 < location.size → ¬location.Earlier start → location.Earlier stop →
    after location.key = before location.key

theorem AgreesBetween.advance {before after : Journal} {start next stop : Location}
    (same : AgreesBetween before after start stop) (later : start.Earlier next) :
    AgreesBetween before after next stop :=
  fun location nonempty notEarlier beforeStop =>
    same location nonempty (fun earlier => notEarlier (earlier.trans later)) beforeStop

theorem AgreesBetween.narrow {before after : Journal} {start stop nearer : Location}
    (same : AgreesBetween before after start stop) (earlier : nearer.Earlier stop) :
    AgreesBetween before after start nearer :=
  fun location nonempty notEarlier beforeStop => same location nonempty notEarlier (beforeStop.trans earlier)

theorem AgreesBetween.command {before after : Journal} {parent : Location} {branch command : Nat}
    (same : AgreesBetween before after (commandLocation parent branch command) (parent.child (branch + 1))) :
    after (commandLocation parent branch command).key = before (commandLocation parent branch command).key :=
  same _ (by simp [commandLocation]) (Location.Earlier.irrefl _)
    (Location.child_earlier_sibling parent branch command (branch + 1) (by omega))

theorem AgreesBetween.next {before after : Journal} {parent : Location} {branch command : Nat}
    (same : AgreesBetween before after (commandLocation parent branch command) (parent.child (branch + 1))) :
    AgreesBetween before after (commandLocation parent branch (command + 1)) (parent.child (branch + 1)) :=
  same.advance (Location.command_earlier parent branch command (command + 1) (by omega))

theorem AgreesBetween.child {before after : Journal} {parent : Location} {branch command : Nat}
    (same : AgreesBetween before after (commandLocation parent branch command) (parent.child (branch + 1)))
    (index : Nat) :
    AgreesBetween before after ((commandLocation parent branch command).child index)
      ((commandLocation parent branch command).child (index + 1)) := by
  apply (same.advance (Location.earlier_child _ index)).narrow
  simpa only [commandLocation, Location.child, Array.push_eq_append] using
    Location.descendants_earlier_sibling parent branch command (branch + 1) #[(index + 1, 0)] (by omega)

theorem FreshBetween.preserve {before after : Journal} {start stop : Location}
    (fresh : FreshBetween before start stop) (same : AgreesBetween before after start stop) :
    FreshBetween after start stop :=
  fun location nonempty notEarlier beforeStop =>
    (same location nonempty notEarlier beforeStop).trans (fresh location nonempty notEarlier beforeStop)

end Journal

end LeanCloud.Proofs
