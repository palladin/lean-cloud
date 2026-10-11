import LeanCloudRuntime.ObjectStore
import LeanCloudTests.Support
import Std.Sync.Mutex

namespace ObjectStoreTests
open Lean LeanCloud LeanCloudRuntime LeanCloudTests

/-- Run unchanged against the in-memory model and every real storage adapter. -/
def contract (store : ObjectStore) (runPrefix : String) : IO Unit := do
  store.ensureContainer
  let records := store.records runPrefix
  let record : ReplayRecord := ⟨ReplayStore.returnRequest, .success (toJson (7 : Nat))⟩
  assertEq (← records.read "missing") none
  let tasks ← (Array.range 8).mapM fun i => IO.asTask (records.create "race"
    { record with outcome := .success (toJson i) }) .dedicated
  let accepted ← tasks.mapM fun task => IO.ofExcept task.get
  let some winner ← records.read "race" | throw (IO.userError "Concurrent create lost the record")
  for result in accepted do assertEq result winner "Writers did not agree on the canonical record"
  assertEq (← records.create "race" record) winner "Retry overwrote canonical record"
  let bytes := "global blobs: λ 🌍\n".toUTF8
  let ref ← store.putBytes bytes
  store.name (runPrefix ++ "/input") ref
  let .ok resolved ← (store.resolve (runPrefix ++ "/input")).run
    | throw (IO.userError "Cannot resolve test blob")
  assertEq resolved ref
  let .ok actual ← (store.readBytes ref).run
    | throw (IO.userError "Cannot read test blob")
  assertEq actual.data bytes.data
  let removed := runPrefix ++ "-remove"
  let retained := removed ++ "-keep"
  discard <| store.createJson retained "keep" (toJson (99 : Nat))
  -- More than one listing page, plus a neighboring run and shared user blobs.
  for i in [:129] do discard <| store.createJson removed s!"key-{i}" (toJson i)
  store.removeRun removed
  store.removeRun removed
  assertTrue (← store.isRemoved removed) "Cleanup lost its durable removal marker"
  for i in [:129] do assertEq (← store.readJson removed s!"key-{i}") none
  assertEq (← store.readJson retained "keep") (some (toJson (99 : Nat)))
  let .ok preserved ← (store.readBytes ref).run
    | throw (IO.userError "Run cleanup removed a user blob")
  assertEq preserved.data bytes.data
  for invalid in #[{ ref with size := ref.size + 1 }, { ref with checksum := ref.checksum + 1 }] do
    assertError (← (store.readBytes invalid).run) .integrity
  assertError (← (store.resolve (runPrefix ++ "/missing")).run) .missingBlob
  let invalidText ← store.putBytes (ByteArray.mk #[255])
  assertError (← (DirectInterpreter.interpret (store.storage)
    (fun _ : Unit => CloudBlob.readText invalidText) ()).run) .invalidUtf8

/-- A small atomic reference model; no provider, database, or transport involved. -/
private def model : IO ObjectStore := do
  let objects ← Std.Mutex.new (#[] : Array (String × ByteArray))
  return {
    ensureContainer := pure ()
    read := fun key => objects.atomically do return ((← get).find? (·.1 == key)).map (·.2)
    create := fun key value => objects.atomically do
      if let some (_, existing) := (← get).find? (·.1 == key) then return existing
      modify (·.push (key, value))
      return value
    list := fun keyPrefix => objects.atomically do
      return ((← get).filter (fun row => row.1.startsWith keyPrefix)).map (·.1) |>.extract 0 17
    erase := fun key => objects.atomically do modify (·.filter (·.1 != key)) }

def run : IO Unit := do
  let store ← model
  contract store "model"
  let ref ← store.putBytes "original".toUTF8
  -- An unavailable provider is not a missing blob and must not be journaled as
  -- an ordinary CloudError by an interpreter.
  let unavailable := { store with read := fun _ => throw (IO.userError "Offline") }
  let failed ← try discard (unavailable.readBytes ref).run; pure false catch _ => pure true
  assertTrue failed "Transport error became a workflow outcome"
  let corrupt := { store with read := fun _ => pure (some "corrupt!".toUTF8) }
  assertError (← (corrupt.readBytes ref).run) .integrity
  let deleted ← IO.mkRef (#[] : Array String)
  let unsafeListing := { store with
    list := fun _ => pure #["objects/unrelated"]
    erase := fun key => deleted.modify (·.push key) }
  let failed ← try unsafeListing.removeRun "bad-list"; pure false catch _ => pure true
  assertTrue failed "Unsafe listing accepted"
  assertTrue (← deleted.get).isEmpty "Invalid listing deleted an unrelated object"
  IO.println "Object store contract: immutable races, names, integrity, paginated cleanup, and transport isolation passed."

end ObjectStoreTests
