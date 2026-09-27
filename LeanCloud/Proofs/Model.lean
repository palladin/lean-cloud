import LeanCloud.Storage

/-! Pure state model for the existing interpreters. Journal state belongs to the
storage layer; primitive effects run in a separate external world. -/

namespace LeanCloud.Proofs
open Lean

abbrev Journal := String → Option Json

namespace Journal

def empty : Journal := fun _ => none

def write (journal : Journal) (key : String) (value : Json) : Journal :=
  fun queriedKey => if queriedKey = key then some value else journal queriedKey

end Journal

/-- Blob behavior remains abstract. The same operations are supplied to both
interpreters. `exec` already carries an action in `StateM World`; none of these
primitive actions can access the separate journal through this interface. -/
structure BlobModel (World : Type) where
  putBlob : ByteArray → ExceptT CloudError (StateM World) BlobRef
  readBlob : BlobRef → ExceptT CloudError (StateM World) ByteArray
  resolveBlob : String → ExceptT CloudError (StateM World) BlobRef

/-- Journal reads are exact, and writes always replace the addressed entry and
succeed. Journal operations preserve the world; blob operations preserve the
journal, including when they return a typed failure. -/
def modelStorage (blobs : BlobModel World) : Storage Journal (StateM World) where
  get key journal := pure (journal key, journal)
  put key value journal := pure (true, journal.write key value)
  putBlob bytes journal := do
    let outcome ← (blobs.putBlob bytes).run
    pure (outcome, journal)
  readBlob ref journal := do
    let outcome ← (blobs.readBlob ref).run
    pure (outcome, journal)
  resolveBlob name journal := do
    let outcome ← (blobs.resolveBlob name).run
    pure (outcome, journal)

/-- The model's read contract includes absence of changes to either state. -/
theorem modelStorage_get (blobs : BlobModel World) (key : String)
    (journal : Journal) (world : World) :
    (modelStorage blobs).get key journal world = ((journal key, journal), world) := rfl

/-- The model's write contract includes acceptance and preservation of the world. -/
theorem modelStorage_put (blobs : BlobModel World) (key : String) (value : Json)
    (journal : Journal) (world : World) :
    (modelStorage blobs).put key value journal world =
      ((true, journal.write key value), world) := rfl

/-- Primitive execution is independent of the replay journal and preserves it.
The result and external-state transition can therefore be used as direct
execution evidence even when replay already has committed records. -/
theorem modelStorage_execute (blobs : BlobModel World) (operation : Operation (StateM World) α)
    (journal : Journal) (world : World) :
    ((modelStorage blobs).execute operation).run journal world =
      let ((outcome, _), nextWorld) := ((modelStorage blobs).execute operation).run Journal.empty world
      ((outcome, journal), nextWorld) := by
  cases operation with
  | exec label body =>
    cases h : body () world with
    | mk value nextWorld =>
      simp [Storage.execute, ExceptT.run, ExceptT.mk, liftM, monadLift,
        MonadLift.monadLift, ExceptT.lift, StateT.lift, Functor.map, StateT.map,
        bind, pure, StateT.bind, StateT.pure, h]
  | putBlob bytes => rfl
  | readBlob ref => rfl
  | resolveBlob name => rfl

theorem modelStorage_execute_direct (blobs : BlobModel World)
    (operation : Operation (StateM World) α) (journal : Journal) (world nextWorld : World)
    (outcome : Except CloudError α)
    (executed : ((modelStorage blobs).execute operation).run journal world =
      ((outcome, journal), nextWorld)) :
    ((modelStorage blobs).execute operation).run Journal.empty world =
      ((outcome, Journal.empty), nextWorld) := by
  have transferred := modelStorage_execute blobs operation journal world
  rw [executed] at transferred
  have emptyRun := modelStorage_execute blobs operation Journal.empty world
  cases run : ((modelStorage blobs).execute operation).run Journal.empty world with
  | mk pair finalWorld => cases pair with
    | mk actual finalJournal =>
      rw [run] at transferred emptyRun
      dsimp only at transferred emptyRun
      rcases transferred with ⟨⟨rfl, _⟩, rfl⟩
      exact emptyRun

end LeanCloud.Proofs
