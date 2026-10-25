import LeanCloudRuntime.Storage
import ObjectStoreTests
import LeanCloudTests.Generated

open Lean LeanCloud LeanCloudRuntime LeanCloudTests

/-- Opt-in provider check. Provisioning and deleting the test container/bucket
belong to the caller. Credential files stay outside the checkout. -/
def main (args : List String) : IO UInt32 := do
  try
    let [path] := args | throw (IO.userError "Usage: cloud_storage_tests STORAGE_CONFIG.json")
    let config ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson? (α := Storage.Config))
    IO.ofExcept config.validate
    let store := config.objects
    let run := s!"storage-{← IO.Process.getPID}-{← IO.monoMsNow}"
    IO.println "Checking immutable writes, blob integrity, and paginated removal"
    ObjectStoreTests.contract store run
    for seed in [:8] do
      IO.println s!"Comparing provider replay for seed {seed}"
      let tree := (generate 3 seed).1
      let program (_ : Unit) : Cloud IO Nat := lower tree (seed % 7)
      let expected ← (DirectInterpreter.interpret store.executionContext program ()).run
      let records := store.records s!"{run}-{seed}"
      let actual ← (SequentialReplay.interpret records store.executionContext 10000 program ()).run
      assertOutcome actual expected
      let replayed ← (SequentialReplay.interpret records store.executionContext 1 program ()).run
      assertOutcome replayed expected
    IO.println "Storage contract and 8 direct/replay/warm-replay comparisons passed."
    return 0
  catch error => IO.eprintln error.toString; return 1
