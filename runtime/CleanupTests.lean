import LeanCloudRuntime.Application
import LeanCloudTests.Support

namespace CleanupTests
open Lean LeanCloud LeanCloudRuntime LeanCloudTests

private def step (worker run : String) : Observations.Step := {
  timestamp := "1"
  event := ⟨"session", 0, 0, worker, some 0, Location.root.key, "idle", "", run, none⟩
  branch := some Location.root }

def run : IO Unit := do
  let connections ← (Array.range 3).mapM fun _ => LeanLinq.Sqlite.connect ":memory:"
  try
    let stores ← connections.mapIdxM fun i conn => ObservationStore.create conn s!"worker{i}"
    let routes : Array HttpMailbox.WorkerEndpoint := (Array.range 3).map fun i =>
      { worker := s!"worker{i}", endpoint := ⟨"127.0.0.1", 1, "test"⟩ }
    for store in stores do
      store.record (step store.worker "retired")
      store.record (step store.worker "kept")
      store.flush
    let visited ← IO.mkRef (#[] : Array String)
    let unavailable ← IO.mkRef true
    let purge (route : HttpMailbox.WorkerEndpoint) := do
      visited.modify (·.push route.worker)
      if route.worker == "worker1" && (← unavailable.get) then
        throw (IO.userError "node unavailable")
      let some store := stores.find? (·.worker == route.worker) | throw (IO.userError "Unknown worker")
      store.remove "retired"
    let error ← try Application.cleanupWorkers routes purge; pure none
      catch error => pure (some error.toString)
    assertTrue (error.any (·.contains "worker1")) "Partial cleanup reported success or hid the failed node"
    assertEq (← visited.get) (routes.map (·.worker)) "Cleanup skipped nodes after failure"
    for i in [:stores.size] do
      let some store := stores[i]? | throw (IO.userError "Missing test store")
      assertEq (← store.page "retired" none 100).items.isEmpty (i != 1)
      assertTrue (!(← store.page "kept" none 100).items.isEmpty) "Cleanup erased another run"
    unavailable.set false
    Application.cleanupWorkers routes purge
    Application.cleanupWorkers routes purge
    for store in stores do
      -- A final trace event can race with removal after the report was accepted.
      store.record (step store.worker "retired")
      assertTrue (← store.page "retired" none 100).items.isEmpty "Late telemetry recreated a retired run"
    let emptyFailed ← try Application.cleanupWorkers #[] purge; pure false catch _ => pure true
    assertTrue emptyFailed "Zero-worker cleanup reported success"
    let (_, removed) ← unwrap (LeanCloud.Pool.command { removed := #["retired"] } .removedRuns)
    assertEq (← unwrap (fromJson? (α := Array String) removed)) #["retired"]
  finally
    for conn in connections do conn.close
  IO.println "Run cleanup: every worker, partial failure, retry, late observations, and run isolation passed."

end CleanupTests
