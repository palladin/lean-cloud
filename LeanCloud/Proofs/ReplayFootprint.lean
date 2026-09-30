import LeanCloud.Proofs.ReplayRelation
import LeanCloud.SimulationBackend
import Init.Data.Range.Lemmas

/-! Primitive footprints for the real journal and replay code. A pure replay
step can update journal records, but none of its own atomic operations change
the queue or final-result field. Concurrent workers remain free to do so. -/

namespace LeanCloud.Proofs
open Lean LeanEff Simulation

def StateUses (allowed : {β : Type} → (δ → β × δ) → Prop)
    (action : StateT σ (SimM δ) α) : Prop := ∀ handle, Uses allowed (action handle)

namespace StateUses
variable {allowed : {β : Type} → (δ → β × δ) → Prop}

theorem pure (value : α) : StateUses allowed (Pure.pure value : StateT σ (SimM δ) α) :=
  fun _ => Uses.pure _ _

theorem bind {first : StateT σ (SimM δ) α} {next : α → StateT σ (SimM δ) β}
    (uses : StateUses allowed first) (rest : ∀ value, StateUses allowed (next value)) :
    StateUses allowed (first >>= next) := fun handle =>
  (uses handle).bind fun pair => rest pair.1 pair.2

theorem except {action : StateT σ (SimM δ) α} (uses : StateUses allowed action) :
    StateUses allowed ((liftM action : ExceptT ε (StateT σ (SimM δ)) α).run) :=
  fun handle => (uses handle).bind fun _ => Uses.pure _ _

theorem except_bind {first : ExceptT ε (StateT σ (SimM δ)) α}
    {next : α → ExceptT ε (StateT σ (SimM δ)) β}
    (uses : StateUses allowed first.run) (rest : ∀ value, StateUses allowed (next value).run) :
    StateUses allowed (first >>= next).run := by
  intro handle
  apply Uses.bind (uses handle)
  intro pair
  cases pair with
  | mk result handle =>
    cases result with
    | ok value => exact rest value handle
    | error error => exact Uses.pure _ _

theorem leased {action : StateT σ (SimM δ) α} (uses : StateUses allowed action) :
    StateUses allowed (LeaseQueue.liftBackend (ρ := ρ) action) :=
  fun worker => (uses worker.backend).bind fun _ => Uses.pure _ _

private theorem forIn (items : List α) (acc : β)
    (body : α → β → StateT σ (SimM δ) (ForInStep β))
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

private theorem pure_bind (value : α) (next : α → StateT σ (SimM δ) β) :
    (Pure.pure value >>= next) = next value := rfl

theorem putSame (db : Db σ (SimM δ))
    (get : ∀ key, StateUses allowed (db.get key))
    (put : ∀ key value, StateUses allowed (db.put key value)) (key : String) (value : Json) :
    StateUses allowed (JournalDb.putSame db key value) := by
  unfold JournalDb.putSame
  apply StateUses.bind (get key)
  intro previous
  cases previous with
  | none => exact put key value
  | some _ => exact .pure _

theorem journal_get (db : Db σ (SimM δ))
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
        simp only [pure_bind]
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

theorem journal_put (db : Db σ (SimM δ))
    (get : ∀ key, StateUses allowed (db.get key))
    (put : ∀ key value, StateUses allowed (db.put key value)) (key : String) (value : Json) :
    StateUses allowed (JournalDb.put db key value) := by
  unfold JournalDb.put
  cases fromJson? (α := Result) value with
  | error error => simp only []; exact .pure _
  | ok record =>
    simp only [pure_bind]
    cases record with
    | completed outcome => exact putSame db get put _ _
    | suspended children =>
      apply StateUses.bind (putSame db get put _ _)
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
            apply StateUses.bind (putSame db get put _ _)
            intro accepted
            cases accepted <;> exact .pure _
        · intro result
          cases result.1 <;> exact .pure _

private def relation (db : Db σ (SimM δ))
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

theorem step (db : Db σ (SimM δ)) (blobs : BlobStorage σ (SimM δ))
    (get : ∀ key, StateUses allowed (db.get key))
    (put : ∀ key value, StateUses allowed (db.put key value)) (fuel : Nat)
    (program : Cloud (SimM δ) Json) (supported : PureProgram program) (location : Location) :
    StateUses allowed (ReplayInterpreter.Internal.step db blobs fuel program location).run :=
  (relation db get put).step blobs blobs fuel program supported location

end StateUses

namespace ReplayFootprint
open SimulationBackend

def JournalOnly {α : Type} (operation : Durable → α × Durable) : Prop :=
  ∀ state, (operation state).2.transport = state.transport ∧ (operation state).2.completed = state.completed

private theorem raw_get (key : String) : StateUses JournalOnly (rawDb.get key) := by
  intro handle
  exact (Uses.atomic _ (fun _ => ⟨rfl, rfl⟩)).bind fun _ => Uses.pure _ _

private theorem raw_put (key : String) (value : Json) : StateUses JournalOnly (rawDb.put key value) := by
  intro handle
  exact (Uses.atomic _ (fun _ => ⟨rfl, rfl⟩)).bind fun _ => Uses.pure _ _

/-- The actual journal-backed, leased replay step touches neither transport
nor the run's separately published final result at any atomic boundary. -/
theorem step (fuel : Nat) (program : Cloud M Json) (supported : PureProgram program)
    (location : Location) (worker : SimulationBackend.Worker) :
    Uses JournalOnly ((ReplayInterpreter.Internal.step db noBlobs fuel program location).run worker) := by
  apply StateUses.step db noBlobs _ _ fuel program supported location worker
  · intro key
    exact (StateUses.journal_get rawDb raw_get key).leased
  · intro key value
    exact (StateUses.journal_put rawDb raw_get raw_put key value).leased

end ReplayFootprint
end LeanCloud.Proofs
