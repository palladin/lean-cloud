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
  assertError (← (DirectInterpreter.interpret (store.executionContext)
    (fun _ : Unit => Cloud.exec (fun env => env.blobs.readText invalidText)) ()).run) .application

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

/-- Two blob reads must overlap within a single command. A lost command commit
may repeat them; a successful commit is reused without any further user IO. -/
private def executionBoundary (objects : ObjectStore) : IO Unit := do
  let ref ← objects.putBytes "parallel blob IO".toUTF8
  for afterCommit in [false, true] do
    let entered ← Std.Mutex.new (0 : Nat)
    let generation ← IO.mkRef 0
    let read : BlobRef → ExceptT CloudError IO ByteArray := fun ref => do
      let ticket ← entered.atomically do
        let count ← get
        set (count + 1)
        return count
      -- Both dedicated tasks must enter before either is allowed to finish.
      let target := ticket / 2 * 2 + 2
      let started ← IO.monoMsNow
      repeat
        if (← entered.atomically get) ≥ target then break
        if (← IO.monoMsNow) - started > 5000 then
          throw ⟨.application, "Blob reads did not run concurrently"⟩
        IO.sleep 1
      objects.executionContext.blobs.readBlob ref
    let context : ExecContext IO := { objects.executionContext with
      blobs := { objects.executionContext.blobs with readBlob := read } }
    let program (_ : Unit) : Cloud IO BlobRef := Cloud.exec (fun env => do
      generation.modify (· + 1)
      let tasks ← #[ref, ref].mapM fun input => IO.asTask (env.blobs.readText input) .dedicated
      -- Drain every task before propagating a user exception.
      let outcomes ← tasks.mapM fun task => (IO.wait task : IO _)
      let values ← outcomes.mapM IO.ofExcept
      env.blobs.putText (String.intercalate "\n" values.toList)) "parallel blob IO"
    let saved ← IO.mkRef ([] : List (String × ReplayRecord))
    let crashed ← IO.mkRef false
    let store : ReplayStore IO := {
      read := fun key => return (← saved.get).lookup key
      create := fun key proposed => do
        let first ← crashed.modifyGet fun old => (!old, true)
        if first && !afterCommit then throw (IO.userError "Worker stopped before commit")
        let accepted ← saved.modifyGet fun records => match records.lookup key with
          | some old => (old, records)
          | none => (proposed, (key, proposed) :: records)
        if first && afterCommit then throw (IO.userError "Worker stopped after commit")
        return accepted }
    let run := (SequentialReplay.interpret store context 100 program ()).run
    let stopped ← try discard run; pure false catch _ => pure true
    assertTrue stopped "Journal interruption became a user failure"
    let .ok result ← run | throw (IO.userError "Restart did not complete")
    assertEq (← generation.get) (if afterCommit then 1 else 2)
    assertEq (← entered.atomically get) (if afterCommit then 2 else 4)
    assertEq (← saved.get).length 2 "Blob IO produced intermediate replay records"
    assertEq ((← saved.get).lookup (ReplayStore.valueKey Location.root)).isSome true
    assertEq (String.fromUTF8? (← IO.ofExcept ((← objects.readBytes result |>.run).mapError (·.message))))
      (some "parallel blob IO\nparallel blob IO")
    assertOutcome (← run) (.ok result)
    assertEq (← generation.get) (if afterCommit then 1 else 2) "Warm replay ran the IO body"
  -- Blob exceptions are catchable by ordinary IO code inside the callback.
  let unavailable := { objects with read := fun _ => throw (IO.userError "Unavailable") }
  let handled (_ : Unit) : Cloud IO String := Cloud.exec fun env => do
    try env.blobs.readText ref catch _ => pure "fallback"
  assertOutcome (← (DirectInterpreter.interpret unavailable.executionContext handled ()).run) (.ok "fallback")
  IO.println "Execution environment: concurrent blob IO, command-only journaling, crash replay and user recovery passed."

def run : IO Unit := do
  digestTests
  let store ← model
  contract store "model"
  executionBoundary store
  let ref ← store.putBytes "original".toUTF8
  -- Raw journal IO must escape; user-facing blob IO must become a recorded failure.
  let unavailable := { store with
    read := fun _ => throw (IO.userError "Offline")
    create := fun _ _ => throw (IO.userError "Offline") }
  let failed ← try discard (unavailable.readBytes ref).run; pure false catch _ => pure true
  assertTrue failed "Raw storage swallowed a transport exception"
  for program in #[
      (do discard <| Cloud.exec (fun env => env.blobs.putText "value") : Cloud IO Unit),
      (do discard <| Cloud.exec (fun env => env.blobs.readBlob ref) : Cloud IO Unit),
      (do discard <| Cloud.exec (fun env => env.blobs.resolveBlob "input") : Cloud IO Unit)] do
    let records ← model
    let journal := records.records "blob-exception"
    let run (blobs : ExecContext IO) :=
      (SequentialReplay.interpret journal blobs 100 (fun _ : Unit => program) ()).run
    assertOutcome (← (DirectInterpreter.interpret unavailable.executionContext (fun _ : Unit => program) ()).run)
      (.error ⟨.application, "Offline"⟩)
    assertOutcome (← run unavailable.executionContext) (.error ⟨.application, "Offline"⟩)
    -- The provider recovers, but replay keeps the original failure.
    assertOutcome (← run store.executionContext) (.error ⟨.application, "Offline"⟩)
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
