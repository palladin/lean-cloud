import LeanCloudRuntime.ReplayCache
import LeanCloudTests.Support
import LeanCloud.SequentialReplay

namespace ReplayCacheTests
open Lean LeanCloud LeanCloudRuntime LeanCloudTests

private def record (n : Nat) : ReplayRecord := ⟨ReplayStore.returnRequest, .success (toJson n)⟩

private def rejects (action : IO α) : IO Unit := do
  let failed ← try discard action; pure false catch _ => pure true
  assertTrue failed "Expected the store/ownership error to escape"

private def laws : IO Unit := do
  let cache ← ReplayCache.create
  let reads ← IO.mkRef 0
  let writes ← IO.mkRef 0
  let guards ← IO.mkRef 0
  let allowed ← IO.mkRef true
  let failing ← IO.mkRef false
  let values ← IO.mkRef ({} : Std.HashMap String ReplayRecord)
  let backing : ReplayStore IO := {
    read := fun key => do
      reads.modify (· + 1)
      if ← failing.get then throw (IO.userError "read failed")
      return (← values.get)[key]?
    create := fun key value => do
      writes.modify (· + 1)
      if ← failing.get then throw (IO.userError "write failed")
      let canonical := (← values.get)[key]?.getD value
      values.modify (·.insert key canonical)
      return canonical }
  let guard := do
    guards.modify (· + 1)
    unless ← allowed.get do throw (IO.userError "revoked")
  let store := cache.records "one" backing guard
  assertEq (← store.read "x") none
  values.modify (·.insert "x" (record 1))
  assertEq (← store.read "x") (some (record 1)) "Absence was cached"
  failing.set true
  assertEq (← store.read "x") (some (record 1))
  assertEq (← reads.get) 2 "Cache hit reached backing storage"
  allowed.set false
  rejects (store.read "x")
  rejects (store.create "x" (record 2))
  allowed.set true
  rejects (store.read "missing")
  rejects (store.create "x" (record 2))
  failing.set false
  assertEq (← store.create "x" (record 2)) (record 1) "Create lost the canonical winner"
  assertEq (← store.read "x") (some (record 1))
  let failure : ReplayRecord := ⟨ReplayStore.returnRequest, .failure ⟨.application, "user IO failed"⟩⟩
  assertEq (← store.create "error" failure) failure
  failing.set true
  assertEq (← store.read "error") (some failure) "Durable application failure was not cached"
  failing.set false
  assertEq (← writes.get) 3 "Cached writes bypassed durable storage or revocation"
  assertEq (← guards.get) 11 "Cache hits bypassed ownership checks"
  values.modify (·.insert "missing" (record 3))
  assertEq (← store.read "missing") (some (record 3)) "A failed read was cached"
  -- A create conflict on a cold key must cache the winner, not our proposal.
  values.modify (·.insert "winner" (record 4))
  assertEq (← store.create "winner" (record 5)) (record 4)
  failing.set true
  assertEq (← store.read "winner") (some (record 4))
  let other := cache.records "two" {
    read := fun _ => pure (some (record 99)), create := fun _ r => pure r } (pure ())
  assertEq (← other.read "x") (some (record 99)) "Cache crossed run IDs"
  cache.remove "one"
  assertEq (← cache.usage).1 1 "Removal erased another run or retained this run"
  failing.set true
  rejects (store.read "x")
  assertEq (← other.read "x") (some (record 99))

private def bounds : IO Unit := do
  let reads ← IO.mkRef 0
  let backing : ReplayStore IO := {
    read := fun _ => do reads.modify (· + 1); return some (record 1)
    create := fun _ r => pure r }
  let bytes := "run".utf8ByteSize + "a".utf8ByteSize + (toJson (record 1)).compress.utf8ByteSize
  for (maxBytes, maxEntries) in [(bytes * 2, 100), (100000, 2)] do
    let cache ← ReplayCache.create maxBytes maxEntries
    let store := cache.records "run" backing (pure ())
    for key in ["a", "b", "c"] do discard (store.read key)
    let (count, used) ← cache.usage
    assertEq count 2
    assertTrue (used ≤ maxBytes) "Cache exceeded byte budget"
    let before ← reads.get
    discard (store.read "b"); discard (store.read "c")
    assertEq (← reads.get) before
    discard (store.read "a")
    assertEq (← reads.get) (before + 1) "Oldest entry was not evicted"
  for (maxBytes, maxEntries) in [(0, 10), (100000, 0), (bytes - 1, 10)] do
    let cache ← ReplayCache.create maxBytes maxEntries
    let store := cache.records "run" backing (pure ())
    let before ← reads.get
    for _ in [:2] do discard (store.read "a")
    assertEq (← reads.get) (before + 2) "Disabled/oversized records entered cache"
    assertEq (← cache.usage) (0, 0)

private def interruptedRemoval : IO Unit := do
  for (write, duringCheck) in [(false, false), (true, false), (false, true), (true, true)] do
    let cache ← ReplayCache.create
    let started ← IO.Promise.new (α := Unit)
    let released ← IO.Promise.new (α := Unit)
    let await : IO Unit := do
      started.resolve ()
      discard <| IO.wait released.result!
    let store := cache.records "retired" {
      read := fun _ => do
        unless duringCheck do await
        return some (record 1)
      create := fun _ _ => do
        unless duringCheck do await
        return record 1 }
      (if duringCheck then await else pure ())
    let task ← IO.asTask (if write then discard (store.create "x" (record 1)) else discard (store.read "x")) .dedicated
    try
      discard <| IO.wait started.result!
      cache.remove "retired"
    finally released.resolve ()
    discard <| IO.ofExcept task.get
    assertEq (← cache.usage) (0, 0) "In-flight operation refilled a removed run"

private def workload (_ : Unit) : Cloud IO Nat := cloud {
  let base ← Cloud.pure (fun _ => 10) "prefix"
  let values ← Cloud.parallel ((Array.range 24).map fun n => cloud {
    let inner ← Cloud.parallel ((Array.range 3).map fun k => cloud {
      Cloud.pure (fun _ => base + n + k) "leaf"
    })
    return inner.foldl (· + ·) 0
  })
  return values.foldl (· + ·) 0
}

/-- Count real interpreter store calls, with the same persistent state and
ownership checks. Caching changes reads only, never results or journal contents. -/
private def differential : IO Unit := do
  let blobs : BlobStorage IO := {
    putBlob := fun _ => throw ⟨.unsupported, "unused"⟩
    readBlob := fun _ => throw ⟨.unsupported, "unused"⟩
    resolveBlob := fun _ => throw ⟨.unsupported, "unused"⟩ }
  let execute (cached : Bool) := do
    let journal ← IO.mkRef ({} : Std.HashMap String ReplayRecord)
    let reads ← IO.mkRef 0
    let checks ← IO.mkRef 0
    let backing : ReplayStore IO := {
      read := fun key => do reads.modify (· + 1); return (← journal.get)[key]?
      create := fun key record => do
        let value := (← journal.get)[key]?.getD record
        journal.modify (·.insert key value)
        return value }
    let cache ← ReplayCache.create (if cached then 1024 * 1024 else 0)
    let store := cache.records "nested" backing (checks.modify (· + 1))
    let value ← (SequentialReplay.interpret store blobs 10000 workload ()).run
    let before ← reads.get
    assertOutcome (← (SequentialReplay.interpret store blobs 10000 workload ()).run) value
    if cached then assertEq (← reads.get) before "Warm replay read backing storage"
    return (value, (← journal.get).toArray.qsort (fun a b => a.1 < b.1), ← reads.get, ← checks.get)
  let (expected, journal, coldReads, coldChecks) ← execute false
  let (actual, cachedJournal, cachedReads, cachedChecks) ← execute true
  assertOutcome actual (← (DirectInterpreter.interpret blobs workload ()).run)
  assertOutcome actual expected
  assertEq cachedJournal journal
  assertEq cachedChecks coldChecks "Caching skipped ownership checks"
  IO.println s!"Replay cache: backing reads {coldReads} → {cachedReads}; {cachedChecks} ownership checks unchanged."
  assertTrue (cachedReads < coldReads) "Nested replay did not reduce storage reads"

def run : IO Unit := do
  laws
  bounds
  interruptedRemoval
  differential
  IO.println "Replay cache: canonical results, failure isolation, revocation, bounds, removal, and differential replay passed."

end ReplayCacheTests
