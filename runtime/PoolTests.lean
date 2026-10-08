import LeanCloudRuntime.Application
import LeanCloudRuntime.Programs
import LeanCloudTests.Support

/-! Pool failure integration tests. The real scheduler runs in a child process,
using the HTTP/SQLite inbox services and S3 fixture. Workers execute the actual
replay interpreter; only their fuel and delivery timing are controlled here. -/
namespace PoolTests
open Lean LeanCloud LeanCloudRuntime LeanCloudTests

private def fuelError : CloudError := ⟨.protocol, "Interpreter fuel exhausted"⟩

private def rejects (action : IO α) : IO Unit := do
  let rejected ← try discard action; pure false catch _ => pure true
  assertTrue rejected "Expected the operation to be rejected"

private def waitOutcome (process : CloudProcess Nat) : IO (Except CloudError Nat) := do
  let deadline := (← IO.monoMsNow) + 10000
  repeat
    if let some result ← process.poll then return result
    unless (← IO.monoMsNow) < deadline do throw (IO.userError "Terminal failure stayed pending")
    IO.sleep 50

private def assignment (config : Config) (handle : HttpMailbox.Handle) (worker run : String) : IO Assignment := do
  LeanCloudRuntime.Pool.send config (.ready worker)
  let inbox : Mailbox IO LeanCloud.Pool.Reply := HttpMailbox.inbox handle
  let deadline := (← IO.monoMsNow) + 10000
  repeat
    unless (← IO.monoMsNow) < deadline do throw (IO.userError "Pool did not assign work")
    let some delivery ← inbox.receive | continue
    inbox.acknowledge delivery.receipt
    if let .execute id job := delivery.message then
      assertEq id run "Assignment crossed run namespaces"
      return job

private def report (config : Config) (run : String) (value : Report) : IO Unit := do
  LeanCloudRuntime.Pool.send config (.report run value)
  -- The real inbox preserves publication order. Wait for this request to pass
  -- the report before inspecting the durable scheduler state or result.
  discard <| LeanCloudRuntime.Pool.request config .health

/-- The coordinator supplies intent and lease; this worker publishes the root
before reporting completion. No scheduler-side record IO is involved. -/
private def finalize (config : Config) (handle : HttpMailbox.Handle) (worker run : String) : IO Unit := do
  LeanCloudRuntime.Pool.send config (.ready worker)
  let inbox : Mailbox IO LeanCloud.Pool.Reply := HttpMailbox.inbox handle
  let deadline := (← IO.monoMsNow) + 10000
  repeat
    unless (← IO.monoMsNow) < deadline do throw (IO.userError "Pool did not assign finalization")
    let some delivery ← inbox.receive | continue
    if let .finalize id attempt outcome := delivery.message then
      assertEq id run
      let value ← Worker.finalize worker (← observe (S3.records config.blobs id)) attempt outcome
      assertOutcome value.progress (.ok .done)
      report config id value
      inbox.acknowledge delivery.receipt
      return
    inbox.acknowledge delivery.receipt

private def execute (config : Config) (run worker : String) (fuel : Nat) (input : Array Nat)
    (job : Assignment) : IO Report := do
  Worker.execute worker (← observe (S3.records config.blobs run)) (S3.storage config.blobs)
    fuel Squares.workflow input job

private def liveFailure (config : Config) (runPrefix : String) : IO Unit := do
  let failed ← sumSquares.submit config (runPrefix ++ "-live-failure") #[2, 3]
  let first ← HttpMailbox.openMailbox (← IO.ofExcept (config.mailboxes.worker "worker1"))
    LeanCloudRuntime.Pool.address "worker.worker1"
  let second ← HttpMailbox.openMailbox (← IO.ofExcept (config.mailboxes.worker "worker2"))
    LeanCloudRuntime.Pool.address "worker.worker2"
  try
    let root ← assignment config first "worker1" failed.id
    report config failed.id (← execute config failed.id "worker1" 1000 #[2, 3] root)
    let left ← assignment config first "worker1" failed.id
    let right ← assignment config second "worker2" failed.id
    assertTrue (left.branchStart != Location.root && right.branchStart != Location.root) "Expected parallel children"
    let failure ← execute config failed.id "worker1" 0 #[2, 3] left
    let .error error := failure.progress | throw (IO.userError "Expected actual interpreter exhaustion")
    assertEq error fuelError
    report config failed.id failure
    assertTrue (← failed.poll).isNone "Scheduler wrote the failure result"
    finalize config first "worker1" failed.id
    assertOutcome (← waitOutcome failed) (.error fuelError)
    assertOutcome (← failed.await) (.error fuelError)
    let state ← LeanCloudRuntime.Pool.status config failed.id
    assertEq state.error (some fuelError)
    for job in [left, right] do
      let worker := if job.attempt == left.attempt then "worker1" else "worker2"
      let valid : Bool ← IO.ofExcept (fromJson? (← LeanCloudRuntime.Pool.request config (.check failed.id worker job.attempt)))
      assertTrue (!valid) "Failure left a sibling assignment valid"
    -- A duplicate failure and a late completed sibling cannot replace the root.
    report config failed.id failure
    report config failed.id (← execute config failed.id "worker2" 1000 #[2, 3] right)
    rejects (LeanCloudRuntime.Pool.request config (.resume failed.id))
    rejects (LeanCloudRuntime.Pool.request config (.pause failed.id))
    discard <| LeanCloudRuntime.Pool.request config (.kill failed.id)
    assertOutcome (← failed.await) (.error fuelError)
    for command in ["outcome", "result"] do
      let output : LeanCloudCli.ProcessOutput ← IO.ofExcept (fromJson? (← Application.api programs config
        (fun _ _ _ => pure ()) (Json.mkObj [("args", toJson #[command, "config", failed.id]), ("input", Json.null)])))
      if command == "result" then
        assertEq output.exitCode 1
        assertTrue ((output.stderr.splitOn fuelError.message).length > 1) "Application omitted the failure reason"
      else
        assertEq (← IO.ofExcept (Json.parse output.stdout >>= fromJson? (α := Option Exit))) (some (.failure fuelError))
    -- An IO transport exception produces no terminal report. The same assignment
    -- can retry, and the shared worker can still complete another workflow.
    let healthy ← sumSquares.submit config (runPrefix ++ "-healthy") #[2, 3]
    let job ← assignment config first "worker1" healthy.id
    let broken : ReplayStore IO := { (S3.records config.blobs healthy.id) with
      read := fun _ => throw (IO.userError "Temporary connection failure") }
    rejects (Worker.execute "worker1" ⟨broken, pure #[]⟩ (S3.storage config.blobs)
      1000 Squares.workflow #[2, 3] job)
    assertTrue (← healthy.poll).isNone "IO exception became a workflow result"
    assertTrue (← LeanCloudRuntime.Pool.status config healthy.id).error.isNone "IO exception terminated the run"
    report config healthy.id (← execute config healthy.id "worker1" 1000 #[2, 3] job)
    for _ in [:8] do
      if (← healthy.poll).isSome then break
      let job ← assignment config first "worker1" healthy.id
      report config healthy.id (← execute config healthy.id "worker1" 1000 #[2, 3] job)
    assertOutcome (← waitOutcome healthy) (.ok 13)
    assertOutcome (← failed.poll).get! (.error fuelError)
  finally
    first.close
    second.close

def run (original : Config) (runPrefix : String) : IO Unit :=
    IO.FS.withTempFile fun _ database => IO.FS.withTempFile fun _ configPath => do
  let config := { original with scheduler := { original.scheduler with database := database.toString } }
  IO.FS.writeFile configPath (toJson config).compress
  -- Durable snapshots at two crash boundaries: before root publication, and
  -- after publication but before report acknowledgement. Also preserve a root
  -- success that committed before the failure intent was accepted.
  let scenarios := #[
    (runPrefix ++ "-before-publication", none, Exit.failure fuelError),
    (runPrefix ++ "-before-ack", some (Exit.failure fuelError), Exit.failure fuelError),
    (runPrefix ++ "-completed-first", some (Exit.success (toJson (29 : Nat))), Exit.success (toJson (29 : Nat)))]
  for (id, existing, _) in scenarios do
    programs.submit config id sumSquares.info.entry (toJson (#[2, 3, 4] : Array Nat))
    if let some outcome := existing then
      let value ← Worker.finalize "test-worker" ⟨S3.records config.blobs id, pure #[]⟩ 0 outcome
      assertOutcome value.progress (.ok .done)
  let conn ← LeanLinq.Sqlite.connect database.toString
  try
    LocalDb.initializeSchema conn
    let state : LeanCloud.Pool.State := { runs := scenarios.map fun (id, _, _) =>
      { id, scheduler := { error := some fuelError, nextAttempt := 7 } } }
    LocalDb.saveValue conn "pool-v1" ({ state } : LeanCloudRuntime.Pool.Saved)
  finally conn.close
  let child ← IO.Process.spawn {
    cmd := (← IO.appPath).toString
    args := #[configPath.toString, "pool-scheduler"], stdout := .piped }
  let logs ← IO.asTask child.stdout.readToEnd .dedicated
  try
    let handle ← HttpMailbox.openMailbox (← IO.ofExcept (config.mailboxes.worker "worker1"))
      LeanCloudRuntime.Pool.address "worker.worker1"
    try
      for (id, _, expected) in scenarios do
        finalize config handle "worker1" id
        let process : CloudProcess Nat := ⟨config, id, sumSquares.info.entry⟩
        let actual ← waitOutcome process
        assertOutcome actual ((ReplayInterpreter.result (m := Id) expected).run)
    finally handle.close
    liveFailure config runPrefix
  finally
    try child.kill catch _ => pure ()
    discard child.wait
    let output ← IO.ofExcept logs.get
    IO.println output
  -- Reopen SQLite after process termination: failure intent remains durable.
  let conn ← LeanLinq.Sqlite.connect database.toString
  try
    let saved : LeanCloudRuntime.Pool.Saved ← LocalDb.loadValue conn "pool-v1" {}
    let some failed := saved.state.runs.find? (·.id == runPrefix ++ "-live-failure")
      | throw (IO.userError "Scheduler lost the failed run")
    assertEq failed.terminalOutcome (some (.failure fuelError))
  finally conn.close

end PoolTests
