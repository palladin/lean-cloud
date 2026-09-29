import LeanCloud.Proofs.JournalRecovery
import LeanCloud.Proofs.CrashSpec

/-! Read refinement for the real journal adapter. Each physical read can stop
the worker; a successful read returns the same view as the ideal exact map. -/

namespace LeanCloud.Proofs.JournalAdapter
open Lean JournalDb CrashModel CrashRecovery

private def ReadRefines (action : StateT Unit (M Journal) α)
    (reference : StateT Journal Id α) : Prop :=
  ∀ journal, Reads (action ()) journal ((reference journal).1, ()) ∧
    (reference journal).2 = journal

private theorem ReadRefines.pure (value : α) :
    ReadRefines (pure value) (pure value) := fun _ => ⟨Reads.pure _ _, rfl⟩

private theorem ReadRefines.bind
    {action : StateT Unit (M Journal) α} {reference : StateT Journal Id α}
    {next : α → StateT Unit (M Journal) β} {referenceNext : α → StateT Journal Id β}
    (first : ReadRefines action reference)
    (rest : ∀ value, ReadRefines (next value) (referenceNext value)) :
    ReadRefines (action >>= next) (reference >>= referenceNext) := by
  intro journal
  have initial := first journal
  have later := rest (reference journal).1 journal
  constructor
  · change Reads ((action >>= next).run ()) journal _
    rw [StateT.run_bind]
    have observation := initial.1.bind (next := fun p => next p.1 p.2) later.1
    change Reads (do let p ← action (); next p.1 p.2) journal
      ((referenceNext (reference journal).1 (reference journal).2).1, ())
    rw [initial.2]
    exact observation
  · change (referenceNext (reference journal).1 (reference journal).2).2 = journal
    rw [initial.2]
    exact later.2

private theorem ReadRefines.get (key : String) :
    ReadRefines (atomicDb.get key) (raw.get key) := by
  intro journal
  exact ⟨Reads.atomic (fun state : Journal => (state key, ())) journal, rfl⟩

private theorem ReadRefines.forIn (items : List α) (acc : β)
    (body : α → β → StateT Unit (M Journal) (ForInStep β))
    (referenceBody : α → β → StateT Journal Id (ForInStep β))
    (spec : ∀ item acc, ReadRefines (body item acc) (referenceBody item acc)) :
    ReadRefines (forIn items acc body) (forIn items acc referenceBody) := by
  induction items generalizing acc with
  | nil => exact .pure _
  | cons item rest ih =>
    simp only [List.forIn_cons]
    apply ReadRefines.bind (spec item acc)
    intro result
    cases result with
    | done value => exact .pure _
    | yield value => exact ih _

private theorem get_refines (key : String) :
    ReadRefines (JournalDb.get atomicDb key) (JournalDb.get raw key) := by
  unfold JournalDb.get
  apply ReadRefines.bind (.get _)
  intro cached
  cases cached with
  | some value =>
    simp only []
    cases fromJson? (α := Exit) value <;> simp only [] <;> exact .pure _
  | none =>
    apply ReadRefines.bind (.get _)
    intro fork
    cases fork with
    | none => exact .pure _
    | some descriptor =>
      simp only []
      cases fromJson? (α := Nat) descriptor with
      | error message => simp only []; exact .pure _
      | ok count =>
        simp only [pure_bind]
        apply ReadRefines.bind
        · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
            Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
          apply ReadRefines.forIn
          intro index acc
          apply ReadRefines.bind (.get _)
          intro child
          cases child with
          | none => exact .pure _
          | some value =>
            simp only []
            cases fromJson? (α := Exit) value <;> simp only [] <;> exact .pure _
        · intro result
          cases result.1 <;> exact .pure _

/-- Successful adapter reads agree with the exact-map interpretation. Crashed
reads leave durable storage unchanged and consume a fault entry. The claim also
covers malformed records, without assuming that decoding succeeds. -/
theorem get_reads (key : String) (journal : Journal) :
    Reads ((JournalDb.get atomicDb key) ()) journal
      ((JournalDb.get raw key journal).1, ()) :=
  (get_refines key journal).1

end LeanCloud.Proofs.JournalAdapter
