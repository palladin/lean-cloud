import LeanCloud.Proofs.RecoveryPrefix
import LeanCloud.Proofs.JournalMerge
import LeanCloud.Proofs.Specification

namespace LeanCloud.Proofs.RecoveryStep
open Lean LeanEff ReplayFaults ReplayModel ReplayInterpreter JournalMerge JournalRegion WorkerRecovery
open Specification RecoveryCursor

/-- A worker may prepend fresh records in its region; every old record remains
unchanged, and every new record agrees with the pure workflow's specification. -/
def Valid (expected base : Journal) (branch : Location) (journal : Journal) : Prop :=
  Writes (Owns branch) base journal ∧ Extends journal expected

variable [rootCodec : Codec α] (source : Cloud WorkerM α)

/-- A dispatchable branch has a reconstructible prefix and a finite remaining
pure evaluation. The same global budget bounds every descendant dispatch. -/
def Ready (expected : Journal) (budget : Nat) (journal : Journal) (branch : Location) : Prop :=
  ∃ (β : Type) (encode : β → Json) (program : Cloud WorkerM β) (outcome : Except CloudError β)
      (current : Location) (cost remaining : Nat),
    branch = Proofs.Location.branchStart current ∧ cost + remaining ≤ budget ∧
    Cursor source journal current encode program cost ∧ Complete expected current program outcome remaining ∧
    expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩

/-- A suspension identifies genuine child computations and at least one missing
return. A completion has the specified durable branch result. -/
def ProgressValid (expected : Journal) (budget : Nat) (branch : Location) : Progress → Journal → Prop
  | .done, journal => ∃ outcome, journal.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩ ∧
      expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩
  | .fork location count, journal => branch = Proofs.Location.branchStart location ∧
      (∀ index : Fin count, Ready source expected budget journal (location.child index)) ∧
      ∃ index : Fin count, journal.lookup (ReplayStore.returnKey (location.child index)) = none

variable {source}

theorem Ready.extend {expected budget before after branch}
    (ready : Ready source expected budget before branch) (grows : Extends before after) :
    Ready source expected budget after branch := by
  obtain ⟨β, encode, program, outcome, current, cost, remaining, same, enough, cursor, meaning, known⟩ := ready
  exact ⟨β, encode, program, outcome, current, cost, remaining, same, enough, cursor.extend source grows, meaning, known⟩

theorem Ready.known {expected budget journal branch} (ready : Ready source expected budget journal branch) :
    ∃ outcome, expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, known⟩ := ready
  exact ⟨_, known⟩

theorem Ready.depth {expected budget journal branch} (ready : Ready source expected budget journal branch) :
    branch.size ≤ budget + 1 := by
  obtain ⟨_, _, _, _, current, cost, remaining, same, enough, cursor, _, _⟩ := ready
  have bounded := (cursor.route source).2
  rw [same, Proofs.Location.branchStart_size]
  omega

/-- Prefix facts survive a fresh write because they concern immutable records. -/
theorem create_preserving {expected base branch key record} (property : Journal → Prop)
    (monotone : ∀ before after, property before → Extends before after → property after)
    (owned : Owns branch key) (known : expected.lookup key = some record) :
    Ensures (Valid expected base branch) (fun j => Valid expected base branch j ∧ property j)
      (liftM (ReplayFaults.store.create key record))
      (fun value journal => property journal ∧ value = record ∧ journal.lookup key = some record) := by
  apply Ensures.atomic (.create key) (ReplayModel.store.create key record) (fun _ h => h.1)
  intro journal ⟨valid, holds⟩
  have created := create_within journal expected key record valid.2 known
  refine ⟨⟨valid.1.trans (Writes.create _ _ _ _ owned), created.2⟩,
    monotone journal _ holds (create_extends journal key record), created.1, ?_⟩
  exact (create_visible journal key record).trans (congrArg some created.1)

theorem finish {expected base branch outcome budget}
    (known : expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩) :
    Ensures (Valid expected base branch) (Valid expected base branch)
      (Internal.finish ReplayFaults.store branch outcome) (ProgressValid source expected budget branch) := by
  unfold Internal.finish ReplayStore.finish
  simp only [bind_assoc]
  apply Ensures.consequence (pre := fun journal => Valid expected base branch journal ∧ True)
    ?_ (fun _ valid => ⟨valid, trivial⟩) (fun _ _ result => result)
  apply (create_preserving (fun _ => True) (fun _ _ _ _ => trivial) (Owns.returned branch) known).bind
  intro record saved ⟨valid, _, same, present⟩
  subst record
  simp only [beq_self_eq_true, ↓reduceIte, pure_bind]
  exact ⟨valid, Nat.le_refl _, outcome, present, known⟩

end LeanCloud.Proofs.RecoveryStep
