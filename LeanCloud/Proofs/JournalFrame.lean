import LeanCloud.Proofs.ReplayRecovery

/-! Physical publication changes only its addressed keys, including after a
crash. This supplies the frame needed to preserve earlier replay prefixes. -/

namespace LeanCloud.Proofs.JournalAdapter
open Lean CrashModel CrashRecovery

/-- Keys outside a publication's footprint retain their exact old contents,
including absence. Merely bounding values by an expected journal is weaker. -/
def Frame (keys : List String) (before after : Journal) : Prop :=
  ∀ key, key ∉ keys → after key = before key

theorem Frame.refl (keys : List String) (journal : Journal) : Frame keys journal journal :=
  fun _ _ => rfl

theorem Frame.write {keys : List String} {initial journal : Journal}
    (kept : Frame keys initial journal) (key : String) (value : Json) (inside : key ∈ keys) :
    Frame keys initial (journal.write key value) := by
  intro other outside
  rw [Journal.read_write_other _ _ _ _ (by intro same; exact outside (same ▸ inside))]
  exact kept other outside

private theorem writeOne_preserves (invariant : Journal → Prop) (key : String) (value : Json)
    (stable : ∀ journal, invariant journal → invariant (journal.write key value)) :
    Triple invariant (writeOne key value) (fun _ journal => invariant journal) invariant := by
  unfold writeOne
  have read : Triple invariant
      (atomic fun journal => (journal key, journal))
      (fun _ journal => invariant journal) invariant :=
    Triple.atomic _ (fun _ h => h) (fun _ h => h) (fun _ h => h)
  apply Triple.bind read
  intro existing
  cases existing with
  | none =>
    exact Triple.atomic _ stable (fun _ h => h) stable
  | some _ => exact (Triple.pure _ _).weaken (fun _ h => h) (fun _ _ h => h.2) (fun _ h => h)

/-- An invariant preserved by each possible write survives the actual
read/check/write loop, including rejection and every committed crash prefix. -/
theorem publication_preserves (invariant : Journal → Prop) (entries : List Record)
    (stable : ∀ entry ∈ entries, ∀ journal, invariant journal → invariant (journal.write entry.1 entry.2)) :
    Triple invariant (publication entries) (fun _ journal => invariant journal) invariant := by
  induction entries with
  | nil => exact (Triple.pure _ _).weaken (fun _ h => h) (fun _ _ h => h.2) (fun _ h => h)
  | cons entry rest ih =>
    obtain ⟨key, value⟩ := entry
    unfold publication
    apply Triple.bind (writeOne_preserves invariant key value (stable (key, value) (by simp)))
    intro accepted
    cases accepted with
    | false => exact (Triple.pure _ _).weaken (fun _ h => h) (fun _ _ h => h.2) (fun _ h => h)
    | true => exact ih (fun entry member => stable entry (by simp [member]))

/-- This footprint law does not require well-formed values or agreement:
a rejected publication and a crashed publication also preserve other keys. -/
theorem publication_frame (keys : List String) (initial : Journal) (entries : List Record)
    (inside : ∀ entry ∈ entries, entry.1 ∈ keys) :
    Triple (Frame keys initial) (publication entries)
      (fun _ journal => Frame keys initial journal) (Frame keys initial) :=
  publication_preserves _ entries (fun entry member _ kept => kept.write entry.1 entry.2 (inside entry member))

end LeanCloud.Proofs.JournalAdapter

namespace LeanCloud.Proofs.ReplayRecovery
open Lean CrashRecovery JournalAdapter ReplayInterpreter.Internal

/-- The interpreter's actual save has the physical adapter's footprint.
Ordinary errors are left unrestricted here; the safety specification excludes
them separately for admitted writes. -/
theorem save_frame (keys : List String) (initial : Journal) (location : Location) (result : Result)
    (inside : ∀ entry ∈ records location.key result, entry.1 ∈ keys) :
    Triple (Frame keys initial) (call (save db location result))
      (fun _ journal => Frame keys initial journal) (Frame keys initial) := by
  rw [call_save]
  exact ((publication_frame keys initial _ inside).map _).weaken
    (fun _ h => h) (fun _ _ ⟨_, _, kept⟩ => kept) (fun _ h => h)

end LeanCloud.Proofs.ReplayRecovery
