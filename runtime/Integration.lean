import LeanCloudRuntime
import LeanCloudRuntime.Programs
import LeanCloudTests.Generated
import PoolTests
import TestServices

open Lean LeanCloud LeanCloudRuntime LeanCloudTests

/-- Exercise the worker's terminal publication without a deployment coordinator. -/
private def finalize (config : Config) (run : String) : IO Exit := do
  let report ← Worker.finalize "test-worker" ⟨S3.records config.blobs run, pure #[]⟩ 0 (.cancelled "Killed by user")
  assertOutcome report.progress (.ok .done)
  let some outcome ← completed config run | throw (IO.userError "Worker did not publish the terminal result")
  return outcome

private def checkPrograms (config : Config) (runPrefix : String) : IO Unit := do
  IO.ofExcept programs.validate
  assertEq programs.programs.size 2
  assertTrue (programs.find "missing/v1").toOption.isNone "Unknown entry accepted"
  let duplicate : Registry := ⟨#[sumSquares.register, sumSquares.register]⟩
  assertTrue duplicate.validate.toOption.isNone "Duplicate entry accepted"
  assertTrue (sumSquares.register.validate (toJson "wrong input")).toOption.isNone "Invalid typed input accepted"
  let input := #[2, 3, 4]
  let process ← sumSquares.submit config (runPrefix ++ "-typed") input
  assertTrue (← process.poll).isNone "New typed process already completed"
  let trace ← Trace.create "registry-test"
  let direct ← (DirectInterpreter.interpret (S3.storage config.blobs) Squares.workflow input).run
  let recorded ← (SequentialReplay.interpret (trace.records (S3.records config.blobs process.id))
    (trace.blobs (S3.storage config.blobs)) 1000
    (fun values => trace.instrument 1000 (Squares.workflow values)) input).run
  assertOutcome recorded direct
  assertOutcome (← process.await) (.ok 29)
  -- A second typed submission is idempotent; incompatible input is rejected.
  discard (sumSquares.submit config process.id input)
  let conflict ← try
    discard (sumSquares.submit config process.id #[9])
    pure false
  catch _ => pure true
  assertTrue conflict "Conflicting typed submission overwrote a run"
  assertEq (← finalize config process.id) (.success (toJson (29 : Nat)))
    "Administrative cancellation overwrote a completed result"
  let killed ← sumSquares.submit config (runPrefix ++ "-killed") input
  for _ in [:2] do
    assertEq (← finalize config killed.id) (.cancelled "Killed by user")
  assertOutcome (← killed.await) (.error ⟨.cancelled, "Killed by user"⟩)
  -- Killing a locally registered run also works if submission never reached S3.
  let unfinished := runPrefix ++ "-unfinished-launch"
  assertEq (← finalize config unfinished) (.cancelled "Killed by user")
  let late ← sumSquares.submit config unfinished input
  assertOutcome (← late.await) (.error ⟨.cancelled, "Killed by user"⟩)

private def checkAdapters (config : Config) (runPrefix : String) : IO Unit := do
  S3.initializeBucket config.blobs
  let records := S3.records config.blobs runPrefix
  let record : ReplayRecord := ⟨ReplayStore.returnRequest, .success (toJson (7 : Nat))⟩
  assertEq (← records.read "missing") none
  let tasks ← (Array.range 8).mapM fun i => IO.asTask (records.create "race"
    { record with outcome := .success (toJson i) }) .dedicated
  let accepted ← tasks.mapM fun task => IO.ofExcept task.get
  let some winner ← records.read "race" | throw (IO.userError "Concurrent create lost the record")
  for result in accepted do assertEq result winner "Writers did not agree on the canonical record"
  assertEq (← records.create "race" record) winner "Retry overwrote canonical record"
  let bytes := "global blobs: λ 🌍\n".toUTF8
  let ref ← S3.putBytes config.blobs bytes
  S3.name config.blobs (runPrefix ++ "/input") ref
  let .ok resolved ← (S3.resolve config.blobs (runPrefix ++ "/input")).run
    | throw (IO.userError "Cannot resolve test blob")
  assertEq resolved ref
  let .ok actual ← (S3.readBytes config.blobs ref).run
    | throw (IO.userError "Cannot read test blob")
  assertEq actual.data bytes.data
  for invalid in #[{ ref with size := ref.size + 1 }, { ref with checksum := ref.checksum + 1 }] do
    assertError (← (S3.readBytes config.blobs invalid).run) .integrity
  assertError (← (S3.resolve config.blobs (runPrefix ++ "/missing")).run) .missingBlob
  let invalidText ← S3.putBytes config.blobs (ByteArray.mk #[255])
  assertError (← (DirectInterpreter.interpret (S3.storage config.blobs)
    (fun _ : Unit => CloudBlob.readText invalidText) ()).run) .invalidUtf8
  IO.FS.withTempFile fun _ path => do
    let conn ← LeanLinq.Sqlite.connect path.toString
    let state := (Scheduler.handle 10 {} (.ready "adapter-worker")).1
    try
      LocalDb.initializeSchema conn
      LocalDb.saveValue conn runPrefix state.catalog
    finally conn.close
    let reopened ← LeanLinq.Sqlite.connect path.toString
    try
      let catalog ← LocalDb.loadValue (α := Scheduler.Catalog) reopened runPrefix {}
      let restored := catalog.restore
      assertEq restored.nextAttempt state.nextAttempt "Attempt counter did not survive reopen"
      assertTrue restored.pending.isEmpty "Restored scheduling tickets from storage"
    finally reopened.close

/-- A confirmed publication can still take time to reach a consumer. Require
the expected payload within a bounded wait instead of assuming immediate delivery. -/
private def receiveAcknowledged (handle : HttpMailbox.Handle) (expected : Nat) : IO Nat := do
  let inbox : Mailbox IO WorkerMessage := HttpMailbox.inbox handle
  for _ in [:40] do
    if let some delivery ← inbox.receive then
      assertEq (toJson delivery.message) (toJson (WorkerMessage.acknowledged expected))
        "Unexpected mailbox payload"
      return delivery.receipt
  throw (IO.userError s!"Missing confirmed message {expected}")

private def checkMailboxes (endpoint : HttpMailbox.Config) (run : String) : IO Unit := do
  let first ← HttpMailbox.openMailbox endpoint run "durability"
  try
    first.send (WorkerMessage.acknowledged 42)
    discard <| receiveAcknowledged first 42
  finally first.close
  -- Closing without ack must retain the delivery through repeated crashes.
  -- Durable inboxes have no finite delivery limit.
  for _ in [:24] do
    let handle ← HttpMailbox.openMailbox endpoint run "durability"
    try discard <| receiveAcknowledged handle 42
    finally handle.close
  let handle ← HttpMailbox.openMailbox endpoint run "durability"
  try
    let inbox : Mailbox IO WorkerMessage := HttpMailbox.inbox handle
    inbox.acknowledge (← receiveAcknowledged handle 42)
  finally handle.close
  -- A receive on the old consumer can time out while 42 is still in flight.
  -- Reopen it and require the next confirmed message, rather than an empty poll.
  let reopened ← HttpMailbox.openMailbox endpoint run "durability"
  try
    reopened.send (WorkerMessage.acknowledged 99)
    let inbox : Mailbox IO WorkerMessage := HttpMailbox.inbox reopened
    inbox.acknowledge (← receiveAcknowledged reopened 99)
    reopened.delete
  finally reopened.close

/-- Identically named queues on different inbox services must retain different values.
Publish while consumers are offline, then read each destination independently. -/
private def checkIsolation (config : Config) (run : String) : IO Unit := do
  let endpoints := #[config.mailboxes.scheduler] ++ config.mailboxes.workers.map (·.endpoint)
  assertTrue (endpoints.size ≥ 4) "Integration tests require a scheduler inbox service and three worker inbox services"
  for i in [:endpoints.size] do
    for j in [:i] do
      assertTrue (endpoints[i]!.host != endpoints[j]!.host || endpoints[i]!.port != endpoints[j]!.port)
        "Integration tests require independent inbox service endpoints"
    HttpMailbox.send endpoints[i]! run "same-name" (WorkerMessage.acknowledged (100 + i))
  for i in [:endpoints.size] do
    let handle ← HttpMailbox.openMailbox endpoints[i]! run "same-name"
    try
      (HttpMailbox.inbox (α := WorkerMessage) handle).acknowledge (← receiveAcknowledged handle (100 + i))
      handle.delete
    finally handle.close
  assertTrue (match config.mailboxes.worker "unconfigured-worker" with | .error _ => true | .ok _ => false)
    "Unknown worker must not use a fallback inbox service"
  let duplicate := { config.mailboxes with workers := config.mailboxes.workers.push config.mailboxes.workers[0]! }
  assertTrue (match duplicate.validate with | .error _ => true | .ok _ => false)
    "Duplicate worker routes must be rejected"
  let invalid := { config.mailboxes with scheduler := { config.mailboxes.scheduler with port := 0 } }
  assertTrue (match invalid.validate with | .error _ => true | .ok _ => false)
    "Invalid inbox service ports must be rejected"

/-- Real HTTP/SQLite ports and S3 exercise the same scheduling core and replay step as Sim. -/
private def compareProgram (config : Config) (run : String) (tree : Tree) (input : Nat) : IO Unit := do
  let program (_ : Unit) : Cloud IO Nat := lower tree input
  let expected ← (DirectInterpreter.interpret (S3.storage config.blobs) program ()).run
  IO.FS.withTempFile fun _ path => do
    let conn ← LeanLinq.Sqlite.connect path.toString
    try
      LocalDb.initializeSchema conn
      let schedulerHandle ← HttpMailbox.openMailbox config.mailboxes.scheduler run "scheduler"
      let nodes := config.mailboxes.workers.extract 0 3
      let handles ← nodes.mapM fun node =>
        HttpMailbox.openMailbox node.endpoint run ("worker." ++ node.worker)
      let records := S3.records config.blobs run
      let workers := handles.mapIdx fun index handle => {
        id := nodes[index]!.worker
        inbox := HttpMailbox.inbox handle
        send := fun message => HttpMailbox.send config.mailboxes.scheduler run "scheduler" message
        observe := ⟨records, pure #[]⟩
        blobs := S3.storage config.blobs : Worker.Ports IO }
      let scheduler : SchedulerPorts IO := {
        inbox := HttpMailbox.inbox schedulerHandle
        localDb := ← TestServices.schedulerStore conn run
        send := fun delivery => do
          let endpoint ← IO.ofExcept (config.mailboxes.worker delivery.worker)
          HttpMailbox.send endpoint run ("worker." ++ delivery.worker) delivery.message }
      try
        let mut states := Array.replicate 3 ({} : Worker.State)
        let mut done := false
        for _ in [:10000] do
          for (worker, index) in workers.toList.zipIdx do
            let some previous := states[index]? | throw (IO.userError "Missing worker state")
            let state ← Worker.turn worker 100000 program () previous
            states := states.set! index state
            Scheduler.turn scheduler 100000
          let state ← scheduler.localDb.load
          if let some error := state.error then throw (IO.userError (reprStr error))
          if state.finished then done := true; break
        assertTrue done "Real backend program did not finish"
        let .ok (some outcome) ← records.outcome.run
          | throw (IO.userError "Missing durable result")
        let actual : Except CloudError Nat := (ReplayInterpreter.result (m := Id) outcome).run
        assertOutcome actual expected
      finally
        schedulerHandle.close
        for handle in handles do handle.close
    finally conn.close

def main (args : List String) : IO UInt32 := do
  try
    let path := args.headD "/etc/lean-cloud/config.json"
    let config ← Config.load path
    match args.drop 1 with
    | ["pool-scheduler"] =>
      LeanCloudRuntime.Pool.scheduler config
      return 0
    | [] => pure ()
    | _ => throw (IO.userError "Invalid integration test arguments")
    TestServices.withMailboxes 4 fun endpoints => do
      let config := { config with mailboxes := ⟨endpoints[0]!,
        (endpoints.extract 1 4).mapIdx fun i endpoint => ⟨s!"worker{i + 1}", endpoint⟩⟩ }
      let runPrefix := s!"properties-{← IO.Process.getPID}-{← IO.monoMsNow}"
      checkAdapters config runPrefix
      PoolTests.run config runPrefix
      checkPrograms config runPrefix
      checkIsolation config runPrefix
      for endpoint in #[config.mailboxes.scheduler] ++ config.mailboxes.workers.map (·.endpoint) do
        checkMailboxes endpoint runPrefix
      for seed in [:16] do
        let tree := (generate 3 seed).1
        try compareProgram config s!"{runPrefix}-{seed}" tree (seed % 7)
        catch error => throw (IO.userError s!"seed={seed}, program={reprStr tree}\n{error}")
      IO.println "Real adapters: pool terminal failure/recovery and retryable IO, independent inbox services, durable redelivery, immutable writes, blob integrity, SQLite recovery, and 16 differential programs passed."
    return 0
  catch error => IO.eprintln error.toString; return 1
