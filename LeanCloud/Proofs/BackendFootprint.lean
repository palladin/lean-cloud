import LeanCloud.Proofs.BackendStep
import LeanCloud.Proofs.ReplayRelation

namespace LeanCloud.Backend.Proofs
open Lean LeanEff LeanCloud.Proofs

def StateUses (allowed : {β : Type} → Request β → Prop)
    (action : StateT σ Replay.M α) : Prop := ∀ handle, Uses allowed ((action handle).run)

namespace StateUses
variable {allowed : {β : Type} → Request β → Prop}

theorem pure (value : α) : StateUses allowed (Pure.pure value : StateT σ Replay.M α) :=
  fun _ => Uses.pure _ _

theorem bind {first : StateT σ Replay.M α} {next : α → StateT σ Replay.M β}
    (uses : StateUses allowed first) (rest : ∀ value, StateUses allowed (next value)) :
    StateUses allowed (first >>= next) := by
  intro handle
  apply Uses.bind (uses handle)
  intro result
  cases result with
  | error error => exact Uses.pure _ _
  | ok pair => exact rest pair.1 pair.2

theorem except {action : StateT σ Replay.M α} (uses : StateUses allowed action) :
    StateUses allowed ((liftM action : ExceptT ε (StateT σ Replay.M) α).run) := by
  change StateUses allowed (action >>= fun value => Pure.pure (Except.ok (ε := ε) value))
  exact uses.bind fun _ => .pure _

theorem except_bind {first : ExceptT ε (StateT σ Replay.M) α}
    {next : α → ExceptT ε (StateT σ Replay.M) β}
    (uses : StateUses allowed first.run) (rest : ∀ value, StateUses allowed (next value).run) :
    StateUses allowed (first >>= next).run := by
  apply StateUses.bind uses
  intro result
  cases result with
  | ok value => exact rest value
  | error error => exact .pure _

theorem leased {action : StateT σ Replay.M α} (uses : StateUses allowed action) :
    StateUses allowed (LeaseQueue.liftBackend (ρ := ρ) action) := by
  intro worker
  apply Uses.bind (uses worker.backend)
  intro result
  cases result <;> exact Uses.pure _ _

theorem forIn (items : List α) (acc : β)
    (body : α → β → StateT σ Replay.M (ForInStep β))
    (uses : ∀ item acc, StateUses allowed (body item acc)) :
    StateUses allowed (forIn items acc body) := by
  induction items generalizing acc with
  | nil => exact .pure _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply StateUses.bind (uses item acc)
    intro result
    cases result with
    | done value => exact .pure _
    | yield value => exact ih value

theorem putSame (db : Db σ Replay.M) (key : String) (value : Json)
    (get : StateUses allowed (db.get key)) (put : StateUses allowed (db.put key value)) :
    StateUses allowed (JournalDb.putSame db key value) := by
  unfold JournalDb.putSame
  apply StateUses.bind get
  intro previous
  cases previous with
  | none => exact put
  | some _ => exact .pure _

theorem journal_get (db : Db σ Replay.M)
    (get : ∀ key, StateUses allowed (db.get key)) (key : String) :
    StateUses allowed (JournalDb.get db key) := by
  unfold JournalDb.get
  apply StateUses.bind (get _)
  intro cached
  cases cached with
  | some value =>
    simp only []
    cases fromJson? (α := Exit) value <;> simp only [] <;> exact .pure _
  | none =>
    apply StateUses.bind (get _)
    intro descriptor
    cases descriptor with
    | none => exact .pure _
    | some descriptor =>
      simp only []
      cases fromJson? (α := Nat) descriptor with
      | error error => simp only []; exact .pure _
      | ok count =>
        simp only [PureBindLaw.pure_bind]
        apply StateUses.bind
        · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
            Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
          apply StateUses.forIn
          intro index acc
          apply StateUses.bind (get _)
          intro child
          cases child with
          | none => exact .pure _
          | some value =>
            simp only []
            cases fromJson? (α := Exit) value <;> simp only [] <;> exact .pure _
        · intro result
          cases result.1 <;> exact .pure _

private def relation (db : Db σ Replay.M)
    (get : ∀ key, StateUses allowed (db.get key))
    (put : ∀ key value, StateUses allowed (db.put key value)) : ReplayRelation db db where
  relates action _ := StateUses allowed action.run
  pure value := .pure _
  throw error := .pure _
  bind := by
    intro α β first second uses left right next
    exact StateUses.except_bind uses next
  get key := (get key).except
  put key value := (put key value).except

theorem step (db : Db σ Replay.M) (blobs : BlobStorage σ Replay.M)
    (get : ∀ key, StateUses allowed (db.get key))
    (put : ∀ key value, StateUses allowed (db.put key value)) (fuel : Nat)
    (program : Cloud Replay.M Json) (supported : PureProgram program) (location : Location) :
    StateUses allowed (ReplayInterpreter.Internal.step db blobs fuel program location).run :=
  (relation db get put).step blobs blobs fuel program supported location

end StateUses

namespace Footprint

/-- The step's own requests may read the Db and update location records.
They cannot change the queue or publish the run's completion record. -/
def JournalOnly : {α : Type} → Request α → Prop
  | _, .get _ => True
  | _, .put key _ => key ≠ CompletionStore.key
  | _, _ => False

private theorem raw_get (key : String) : StateUses JournalOnly (Replay.rawDb.get key) := by
  intro handle
  exact ⟨trivial, fun _ => trivial⟩

private theorem raw_put (key : String) (value : Json) (separate : key ≠ CompletionStore.key) :
    StateUses JournalOnly (Replay.rawDb.put key value) := by
  intro handle
  exact ⟨separate, fun _ => trivial⟩

private theorem putSame (key : String) (value : Json) (separate : key ≠ CompletionStore.key) :
    StateUses JournalOnly (JournalDb.putSame Replay.rawDb key value) :=
  StateUses.putSame Replay.rawDb key value (raw_get key) (raw_put key value separate)

private theorem journal_put (key : String) (value : Json) :
    StateUses JournalOnly (JournalDb.put Replay.rawDb key value) := by
  unfold JournalDb.put
  cases fromJson? (α := Result) value with
  | error error => simp only []; exact .pure _
  | ok record =>
    simp only [PureBindLaw.pure_bind]
    cases record with
    | completed outcome => exact putSame _ _ (Journal.result_separate key)
    | suspended children =>
      apply StateUses.bind (putSame _ _ (Journal.fork_separate key))
      intro accepted
      cases accepted with
      | false => exact .pure _
      | true =>
        simp only [↓reduceIte]
        apply StateUses.bind
        · simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
            Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
          apply StateUses.forIn
          intro index acc
          cases children[index]! with
          | none => exact .pure _
          | some outcome =>
            apply StateUses.bind (putSame _ _ (Journal.child_separate key index))
            intro accepted
            cases accepted <;> exact .pure _
        · intro result
          cases result.1 <;> exact .pure _

theorem step (fuel : Nat) (program : Cloud Replay.M Json) (supported : PureProgram program)
    (location : Location) (worker : Replay.Worker) :
    Uses JournalOnly (((ReplayInterpreter.Internal.step Replay.db Replay.noBlobs fuel program location).run worker).run) := by
  apply StateUses.step Replay.db Replay.noBlobs _ _ fuel program supported location worker
  · intro key
    exact (StateUses.journal_get Replay.rawDb raw_get key).leased
  · intro key value
    exact (journal_put key value).leased

end Footprint
end LeanCloud.Backend.Proofs
