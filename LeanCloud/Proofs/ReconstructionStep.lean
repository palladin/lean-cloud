import LeanCloud.Proofs.TreeRouting
import LeanCloud.Proofs.ReplayStep

/-! The actual replay traversal through recorded prefixes. Every physical read
can still crash; a successful prefix reconstructs the original continuation. -/

namespace LeanCloud.Proofs.ReplayRecovery
open Lean LeanEff CrashModel JournalAdapter ReplayInterpreter.Internal

/-- A read-only prefix can lead into a state-changing target action. A crash in
the prefix leaves the original journal, which must satisfy the outer invariant. -/
theorem load_then (journal : Journal) (location : Location) (record : Option Result)
    (view : JournalDb.get raw location.key journal = (record.map toJson, journal))
    (next : Option Result → Worker α) (post : α → Journal → Prop) (stopped : Journal → Prop)
    (safe : stopped journal) (rest : Spec (· = journal) (next record) post stopped) :
    Spec (· = journal) (load db location >>= next) post stopped := by
  apply Spec.bind ((load_spec location (· = journal)
    (fun returned final => returned = record ∧ final = journal) (by
      intro final same
      subst final
      exact ⟨record, view, rfl, rfl⟩)).weaken
        (fun _ h => h) (fun _ _ h => h) (fun _ h => h ▸ safe))
  intro returned start ⟨same, unchanged⟩
  subst returned
  exact rest start unchanged

/-- At the selected fork, a compatible read has exactly three cases: create
the group, consume its result, or publish its missing children. The safety,
coverage, and progress proofs supply their own postconditions for these cases. -/
theorem fork_cases {m : Type → Type} {program : Cloud m Json} {tree current children outcome next}
    (expansion : Expansion program tree)
    (member : (current, ExecutionTree.fork children outcome next) ∈ tree.nodes Location.root)
    (journal : Journal) (bounded : Extends journal (tree.journal Location.root))
    (blobs : BlobStorage Unit (M Journal)) (fuel : Nat)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud (M Journal) α)
    (continuation : ArrsF (Control (M Journal)) (Array α) Json) (size : children.length = count)
    {post : StepResult → Journal → Prop} {stopped : Journal → Prop} (safe : stopped journal)
    (fresh : JournalDb.get raw current.key journal = (none, journal) →
      Spec (· = journal) (do
        save db current (Result.settle (Array.replicate count none))
        pure (.runnable (if count == 0 then #[current] else Array.ofFn fun i : Fin count => current.child i.val)))
        post stopped)
    (completed : JournalDb.get raw current.key journal =
      (some (toJson (Result.completed (encodeOutcome (inferInstance : Codec Json) outcome))), journal) →
      Spec (· = journal)
        (match encodeOutcome (inferInstance : Codec Json) outcome with
         | .success value => do
           let _ ← decodeGroup codec count value
           pure (.runnable #[current.next])
         | result => finish db current result) post stopped)
    (suspended : ∀ slots : Array (Option Exit), JournalDb.get raw current.key journal =
      (some (toJson (Result.suspended slots)), journal) →
      Spec (· = journal) (pure (.runnable ((Array.ofFn fun i : Fin count => i.val).filterMap fun i =>
        if slots[i]!.isNone then some (current.child i) else none))) post stopped) :
    Spec (· = journal)
      (walk db blobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current current)
      post stopped := by
  obtain ⟨record, view, admitted⟩ := expansion.fork_view (by simp [Location.root]) member journal bounded
  rw [walk]
  apply load_then journal current record view _ _ _ safe
  cases record with
  | none => simpa only [beq_self_eq_true, Option.isNone_none, Bool.and_self, ↓reduceIte] using fresh view
  | some record =>
    have allowed := admitted record rfl
    simp only [beq_self_eq_true, Option.isNone_some, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    cases record with
    | completed result =>
      change result = encodeOutcome (inferInstance : Codec Json) outcome at allowed
      subst result
      have done := completed view
      cases encoded : encodeOutcome (inferInstance : Codec Json) outcome <;>
        simpa only [encoded, beq_self_eq_true, ↓reduceIte] using done
    | suspended slots =>
      have slotSize : slots.size = count := allowed.1.trans size
      simpa only [slotSize, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] using suspended slots view

/-- A recorded successful fork decodes to its original typed values, then
continues at the next command. No primitive user effect is executed. -/
theorem walk_after_join (journal : Journal) (blobs : BlobStorage Unit (M Journal)) (fuel : Nat)
    (codec : Codec α) (law : CodecLaw codec) (count : Nat) (branches : Fin count → Cloud (M Journal) α)
    (continuation : ArrsF (Control (M Journal)) (Array α) Json) (values : Array α)
    (current target : Location) (size : values.size = count) (different : current ≠ target)
    (view : JournalDb.get raw current.key journal =
      (some (toJson (Result.completed (.success (.arr (values.map codec.encode))))), journal))
    (post : StepResult → Journal → Prop) (stopped : Journal → Prop) (safe : stopped journal)
    (rest : Spec (· = journal)
      (walk db blobs fuel (ArrsF.apply continuation values) current.next target) post stopped) :
    Spec (· = journal)
      (walk db blobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current target)
      post stopped := by
  rw [walk]
  apply load_then journal current (some (.completed (.success (.arr (values.map codec.encode))))) view
    _ post stopped safe
  simpa only [beq_eq_false_iff_ne.mpr different, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    ← size, ReplayModel.decode_group_encoded codec law values, pure_bind] using rest

/-- A suspended fork selects the branch identified by the target location;
the closure remains the original branch from the original program. -/
theorem walk_into_child (journal : Journal) (blobs : BlobStorage Unit (M Journal)) (fuel : Nat)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud (M Journal) α)
    (continuation : ArrsF (Control (M Journal)) (Array α) Json)
    (current target : Location) (slots : Array (Option Exit)) (size : slots.size = count)
    (enters : current.entersChild target = true) (index : Fin count)
    (selected : target[current.size]!.1 = index.val)
    (view : JournalDb.get raw current.key journal = (some (toJson (Result.suspended slots)), journal))
    (post : StepResult → Journal → Prop) (stopped : Journal → Prop) (safe : stopped journal)
    (rest : Spec (· = journal)
      (walk db blobs fuel (codec.encode <$> branches index) (current.child index.val) target) post stopped) :
    Spec (· = journal)
      (walk db blobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current target)
      post stopped := by
  have different : current ≠ target := by
    intro same
    subst target
    simp [Location.entersChild] at enters
  rw [walk]
  apply load_then journal current (some (.suspended slots)) view _ post stopped safe
  simpa only [beq_eq_false_iff_ne.mpr different, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    size, bne_self_eq_false, enters, Bool.not_true, selected, index.isLt, ↓reduceDIte] using rest

end LeanCloud.Proofs.ReplayRecovery
