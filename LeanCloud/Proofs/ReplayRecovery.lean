import LeanCloud.Proofs.JournalRead
import LeanCloud.ReplayInterpreter

/-! Crash specifications of the interpreter's actual database operations.
The unit handle is worker-local; the journal and faults survive interruption. -/

namespace LeanCloud.Proofs.ReplayRecovery
open Lean CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

abbrev Worker (α : Type) := ExceptT CloudError (StateT Unit (M Journal)) α

def call (action : Worker α) : M Journal (Except CloudError α) :=
  Prod.fst <$> action.run ()

theorem call_pure (value : α) : call (pure value) = pure (.ok value) := rfl

theorem call_bind (action : Worker α) (next : α → Worker β) :
    call (action >>= next) = (do
      match ← call action with
      | .ok value => call (next value)
      | .error error => pure (.error error)) := by
  funext state
  simp only [call, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.map,
    ExceptT.mk, StateT.bind, bind, pure, Functor.map]
  cases executed : action () state with
  | mk result committed =>
    cases result with
    | error crash => rfl
    | ok value =>
      rcases value with ⟨outcome, handle⟩
      cases handle
      cases outcome <;> rfl

/-- In addition to crash safety, the interpreter call has no ordinary error.
This separates workflow errors encoded as `Exit.failure` from protocol errors. -/
def Spec (pre : Journal → Prop) (action : Worker α)
    (post : α → Journal → Prop) (stopped : Journal → Prop) : Prop :=
  Triple pre (call action)
    (fun outcome journal => ∃ value, outcome = .ok value ∧ post value journal) stopped

theorem Spec.pure (pre : Journal → Prop) (value : α) :
    Spec pre (pure value) (fun result journal => result = value ∧ pre journal) stopped := by
  rw [Spec, call_pure]
  exact (Triple.pure pre (Except.ok (ε := CloudError) value)).weaken (fun _ h => h)
    (fun _ _ ⟨same, valid⟩ => ⟨value, same, rfl, valid⟩) (fun _ h => h)

/-- Returning a value leaves the observed journal untouched. -/
theorem Spec.return_at {journal : Journal} {value : α} {post stopped}
    (valid : post value journal) : Spec (· = journal) (Pure.pure value) post stopped :=
  fun _ same => ⟨Nat.le_refl _, value, rfl, same ▸ valid⟩

theorem Spec.weaken {pre pre' : Journal → Prop} {action : Worker α} {post post' stopped stopped'}
    (spec : Spec pre action post stopped)
    (before : ∀ journal, pre' journal → pre journal)
    (returned : ∀ value journal, post value journal → post' value journal)
    (interrupted : ∀ journal, stopped journal → stopped' journal) :
    Spec pre' action post' stopped' :=
  Triple.weaken spec before
    (fun _ _ ⟨value, same, valid⟩ => ⟨value, same, returned _ _ valid⟩) interrupted

theorem Spec.bind {pre : Journal → Prop} {action : Worker α} {next : α → Worker β}
    {middle post stopped}
    (first : Spec pre action middle stopped)
    (rest : ∀ value, Spec (middle value) (next value) post stopped) :
    Spec pre (action >>= next) post stopped := by
  unfold Spec
  rw [call_bind]
  apply Triple.bind first
  intro outcome start ⟨value, same, valid⟩
  subst outcome
  exact rest value start valid

/-- Combine a result specification with an independently preserved durable
invariant for the same actual call. Crashes retain both interruption facts. -/
theorem Spec.preserve {pre : Journal → Prop} {action : Worker α} {post stopped invariant}
    (spec : Spec pre action post stopped)
    (preserved : Triple invariant (call action) (fun _ journal => invariant journal) invariant) :
    Spec (fun journal => pre journal ∧ invariant journal) action
      (fun value journal => post value journal ∧ invariant journal)
      (fun journal => stopped journal ∧ invariant journal) := by
  exact (Triple.conjoin spec preserved).weaken (fun _ h => h)
    (fun _ _ ⟨⟨value, same, valid⟩, kept⟩ => ⟨value, same, valid, kept⟩) (fun _ h => h)

def db : Db Unit (M Journal) := JournalDb.ofDb atomicDb

private def decodeRecord : Option Json → Except CloudError (Option Result)
  | none => .ok none
  | some value => match fromJson? value with
    | .ok result => .ok (some result)
    | .error message => .error ⟨.codec, message⟩

theorem call_lift (action : StateT Unit (M Journal) α) :
    call (liftM action) = (fun pair => Except.ok pair.1) <$> action () := by
  unfold call
  change Prod.fst <$> ((fun pair => (Except.ok pair.1, pair.2)) <$> action ()) = _
  simp only [Functor.map_map]

private theorem call_load (location : Location) :
    call (load db location) =
      (fun pair => decodeRecord pair.1) <$> (JournalDb.get atomicDb location.key) () := by
  rw [load, call_bind, call_lift]
  simp only [bind_map_left]
  rw [← bind_pure_comp]
  congr 1
  funext pair
  cases pair.1 with
  | none => rfl
  | some value =>
    simp only [decodeRecord]
    cases fromJson? (α := Result) value <;> rfl

/-- Every physical read remains a crash boundary, but a successful `load`
observes precisely the logical record reconstructed by the adapter. -/
theorem load_reads (location : Location) (journal : Journal) (record : Option Result)
    (view : JournalDb.get raw location.key journal = (record.map toJson, journal)) :
    Reads (call (load db location)) journal (.ok record) := by
  rw [call_load]
  have read := (get_reads location.key journal).map (fun pair => decodeRecord pair.1)
  rw [view] at read
  cases record with
  | none => exact read
  | some result => simpa only [Option.map_some, decodeRecord, result_roundtrip] using read

/-- A well-formed logical view gives a specification for the actual interpreter
load, with the same durable invariant on interruption. -/
theorem load_spec (location : Location) (pre : Journal → Prop)
    (post : Option Result → Journal → Prop)
    (view : ∀ journal, pre journal → ∃ record,
      JournalDb.get raw location.key journal = (record.map toJson, journal) ∧ post record journal) :
    Spec pre (load db location) post pre := by
  intro start valid
  obtain ⟨record, observed, returned⟩ := view start.durable valid
  have safe := load_reads location start.durable record observed start rfl
  generalize execution : (call (load db location)).run start = run at *
  rcases run with ⟨outcome, final⟩
  refine ⟨safe.1, ?_⟩
  cases outcome with
  | ok value => exact ⟨record, safe.2.1, safe.2.2 ▸ returned⟩
  | error crash => exact ⟨safe.2.1 ▸ valid, safe.2.2⟩

/-- A redelivered child whose parent has completed is obsolete. The actual
worker entry point reads that parent and republishes its join, without descending
through the already completed fork or writing any records. -/
theorem step_completed_parent_reads (journal : Journal)
    (location parent : Location) (index : Nat) (outcome : Exit)
    (valid : (location.isEmpty || location[0]!.1 != 0) = false)
    (linked : location.parent? = some (parent, index))
    (recorded : JournalDb.get raw parent.key journal =
      (some (toJson (Result.completed outcome)), journal))
    (blobs : BlobStorage Unit (M Journal)) (fuel : Nat) (program : Cloud (M Journal) Json) :
    Reads (call (step db blobs fuel program location)) journal (.ok (.runnable #[parent])) := by
  unfold step
  simp only [valid, Bool.false_eq_true, ↓reduceIte, linked, call_bind]
  apply Reads.bind (load_reads parent journal (some (.completed outcome)) recorded)
  exact Reads.pure _ _

theorem call_save (location : Location) (result : Result) :
    call (save db location result) =
      (fun accepted => if accepted then Except.ok () else
        Except.error (⟨.protocol, s!"Db rejected result at {location.key}"⟩ : CloudError)) <$>
        publication (records location.key result) := by
  rw [save, call_bind, call_lift]
  change ((fun pair => Except.ok pair.1) <$> (JournalDb.put atomicDb location.key (toJson result)) () >>= _) = _
  rw [put_atomic]
  simp only [Functor.map_map, bind_map_left]
  rw [← bind_pure_comp]
  congr 1
  funext accepted
  cases accepted <;> rfl

/-- Any invariant closed under compatible immutable additions survives a save,
including on interruption. This retains facts established by earlier writes. -/
theorem save_preserves (expected : Journal) (invariant : Journal → Prop)
    (location : Location) (result : Result)
    (agrees : Agrees (records location.key result) expected)
    (bounded : ∀ journal, invariant journal → Extends journal expected)
    (stable : ∀ before after, invariant before → Extends before after →
      Extends after expected → invariant after) :
    Spec invariant (save db location result)
      (fun _ journal => invariant journal ∧ Published (records location.key result) journal)
      invariant := by
  unfold Spec
  rw [call_save]
  exact ((publication_spec expected invariant _ agrees bounded stable).map _).weaken
    (fun _ h => h)
    (fun _ _ ⟨accepted, same, acceptedTrue, valid, recorded⟩ => by
      subst accepted
      exact ⟨(), same, valid, recorded⟩) (fun _ h => h)

/-- Save either publishes its records or retains a compatible committed prefix.
All pre-existing records survive; rejected writes cannot occur under agreement. -/
theorem save_spec (expected initial : Journal) (location : Location) (result : Result)
    (agrees : Agrees (records location.key result) expected) :
    Spec (fun journal => Extends initial journal ∧ Extends journal expected)
      (save db location result)
      (fun _ journal => Extends initial journal ∧ Extends journal expected ∧
        Published (records location.key result) journal)
      (fun journal => Extends initial journal ∧ Extends journal expected) := by
  exact (save_preserves expected (fun journal => Extends initial journal ∧ Extends journal expected)
    location result agrees (fun _ h => h.2)
    (fun _ _ h growth bound => ⟨h.1.trans growth, bound⟩)).weaken
      (fun _ h => h) (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ h => h)


end LeanCloud.Proofs.ReplayRecovery
