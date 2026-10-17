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

private def digestTests : IO Unit := do
  for (text, hash) in #[
      ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
      ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") ] do
    assertEq (← Digest.bytes text.toUTF8) hash "SHA-256 known vector"
  IO.FS.withTempDir fun root => do
    let path := root / "source"
    let bytes := ByteArray.mk ((Array.range 200003).map (fun n => (n % 251).toUInt8))
    IO.FS.writeBinFile path bytes
    let expected ← IO.Process.output { cmd := "openssl", args := #["dgst", "-sha256", "-r", path.toString] }
    assertEq expected.exitCode 0
    let hash := (expected.stdout.splitOn " ").head!
    assertEq (← Digest.bytes bytes) hash
    assertEq (← Digest.file path.toString) hash
    for (offset, count) in #[(0, 0), (0, bytes.size), (13, 131073), (bytes.size, 0)] do
      let output := root / "range"
      assertEq (← Digest.copyRange path.toString output.toString offset.toUInt64 count.toUInt64)
        (← Digest.bytes (bytes.extract offset (offset + count)))
      assertEq (← IO.FS.readBinFile output).data (bytes.extract offset (offset + count)).data
    for (offset, count) in #[(bytes.size, 1), (bytes.size + 1, 0)] do
      let rejected ← try
        discard <| Digest.copyRange path.toString (root / "bad").toString offset.toUInt64 count.toUInt64
        pure false
      catch _ => pure true
      assertTrue rejected "Out-of-bounds packed file range accepted"
  IO.println "Native SHA-256: known vectors, OpenSSL comparison, and bounded range copies passed."

def run : IO Unit := do
  digestTests
  let store ← model
  contract store "model"
  let ref ← store.putBytes "original".toUTF8
  -- Raw journal IO must escape; user-facing blob IO must become a recorded failure.
  let unavailable := { store with
    read := fun _ => throw (IO.userError "Offline")
    create := fun _ _ => throw (IO.userError "Offline") }
  let failed ← try discard (unavailable.readBytes ref).run; pure false catch _ => pure true
  assertTrue failed "Raw storage swallowed a transport exception"
  for program in #[
      (do discard <| CloudBlob.putText "value" : Cloud IO Unit),
      (do discard <| CloudBlob.readBytes ref : Cloud IO Unit),
      (do discard <| CloudBlob.resolve "input" : Cloud IO Unit)] do
    let records ← model
    let journal := records.records "blob-exception"
    let run (blobs : BlobStorage IO) :=
      (SequentialReplay.interpret journal blobs 100 (fun _ : Unit => program) ()).run
    assertOutcome (← (DirectInterpreter.interpret unavailable.storage (fun _ : Unit => program) ()).run)
      (.error ⟨.application, "Offline"⟩)
    assertOutcome (← run unavailable.storage) (.error ⟨.application, "Offline"⟩)
    -- The provider recovers, but replay keeps the original failure.
    assertOutcome (← run store.storage) (.error ⟨.application, "Offline"⟩)
  let failed ← try discard <| (unavailable.records "journal-failure").read "key"; pure false catch _ => pure true
  assertTrue failed "Journal failure was confused with a user blob outcome"
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
