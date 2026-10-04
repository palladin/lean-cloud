import LeanCloudRuntime
import LeanCloudRuntime.Programs
import ApplicationTests
import LeanCloudTests.Generated

open Lean LeanCloud LeanCloudRuntime LeanCloudTests

private def checkPrograms (config : Config) (runPrefix : String) : IO Unit := do
  ApplicationTests.run
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
  assertEq (← cancel config process.id) (.success (toJson (29 : Nat)))
    "Administrative cancellation overwrote a completed result"
  let killed ← sumSquares.submit config (runPrefix ++ "-killed") input
  for _ in [:2] do
    assertEq (← cancel config killed.id) (.cancelled "Killed by user")
  assertOutcome (← killed.await) (.error ⟨.cancelled, "Killed by user"⟩)
  -- Killing a locally registered run also works if submission never reached S3.
  let unfinished := runPrefix ++ "-unfinished-launch"
  assertEq (← cancel config unfinished) (.cancelled "Killed by user")
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
      LocalDb.save conn runPrefix state
    finally conn.close
    let reopened ← LeanLinq.Sqlite.connect path.toString
    try assertEq (← LocalDb.load reopened runPrefix) state "Scheduler state did not survive reopen"
    finally reopened.close

/-- A confirmed publication can still take time to reach a consumer. Require
the expected payload within a bounded wait instead of assuming immediate delivery. -/
private def receiveAcknowledged (handle : RabbitMQ.Handle) (expected : Nat) : IO Nat := do
  let inbox : Mailbox IO WorkerMessage := RabbitMQ.inbox handle
  for _ in [:40] do
    if let some delivery ← inbox.receive then
      assertEq (toJson delivery.message) (toJson (WorkerMessage.acknowledged expected))
        "Unexpected mailbox payload"
      return delivery.receipt
  throw (IO.userError s!"Missing confirmed message {expected}")

private def checkMailboxes (broker : RabbitMQ.Config) (run : String) : IO Unit := do
  let first ← RabbitMQ.openMailbox broker run "durability"
  try
    first.send (WorkerMessage.acknowledged 42)
    discard <| receiveAcknowledged first 42
  finally first.close
  -- Closing without ack must retain the delivery through repeated crashes.
  -- The reference classic queues have no finite delivery limit.
  for _ in [:24] do
    let handle ← RabbitMQ.openMailbox broker run "durability"
    try discard <| receiveAcknowledged handle 42
    finally handle.close
  let handle ← RabbitMQ.openMailbox broker run "durability"
  try
    let inbox : Mailbox IO WorkerMessage := RabbitMQ.inbox handle
    inbox.acknowledge (← receiveAcknowledged handle 42)
  finally handle.close
  -- A receive on the old consumer can time out while 42 is still in flight.
  -- Reopen it and require the next confirmed message, rather than an empty poll.
  let reopened ← RabbitMQ.openMailbox broker run "durability"
  try
    reopened.send (WorkerMessage.acknowledged 99)
    let inbox : Mailbox IO WorkerMessage := RabbitMQ.inbox reopened
    inbox.acknowledge (← receiveAcknowledged reopened 99)
    reopened.delete
  finally reopened.close

/-- Identically named queues on different brokers must retain different values.
Publish while consumers are offline, then read each destination independently. -/
private def checkIsolation (config : Config) (run : String) : IO Unit := do
  let brokers := #[config.mailboxes.scheduler] ++ config.mailboxes.workers.map (·.broker)
  assertTrue (brokers.size ≥ 4) "Integration tests require a scheduler broker and three worker brokers"
  for i in [:brokers.size] do
    for j in [:i] do
      assertTrue (brokers[i]!.host != brokers[j]!.host || brokers[i]!.port != brokers[j]!.port)
        "Integration tests require independent broker endpoints"
    RabbitMQ.send brokers[i]! run "same-name" (WorkerMessage.acknowledged (100 + i))
  for i in [:brokers.size] do
    let handle ← RabbitMQ.openMailbox brokers[i]! run "same-name"
    try
      (RabbitMQ.inbox (α := WorkerMessage) handle).acknowledge (← receiveAcknowledged handle (100 + i))
      handle.delete
    finally handle.close
  assertTrue (match config.mailboxes.worker "unconfigured-worker" with | .error _ => true | .ok _ => false)
    "Unknown worker must not use a fallback broker"
  let duplicate := { config.mailboxes with workers := config.mailboxes.workers.push config.mailboxes.workers[0]! }
  assertTrue (match duplicate.validate with | .error _ => true | .ok _ => false)
    "Duplicate worker routes must be rejected"
  let invalid := { config.mailboxes with scheduler := { config.mailboxes.scheduler with port := 0 } }
  assertTrue (match invalid.validate with | .error _ => true | .ok _ => false)
    "Invalid broker ports must be rejected"

/-- Separate RabbitMQ brokers, SQLite, and S3 run the same actor turns as Sim. -/
private def compareProgram (config : Config) (run : String) (tree : Tree) (input : Nat) : IO Unit := do
  let program (_ : Unit) : Cloud IO Nat := lower tree input
  let expected ← (DirectInterpreter.interpret (S3.storage config.blobs) program ()).run
  IO.FS.withTempFile fun _ path => do
    let conn ← LeanLinq.Sqlite.connect path.toString
    try
      LocalDb.initializeSchema conn
      let schedulerHandle ← RabbitMQ.openMailbox config.mailboxes.scheduler run "scheduler"
      let nodes := config.mailboxes.workers.extract 0 3
      let handles ← nodes.mapM fun node =>
        RabbitMQ.openMailbox node.broker run ("worker." ++ node.worker)
      let records := S3.records config.blobs run
      let workers := handles.mapIdx fun index handle => {
        id := nodes[index]!.worker
        inbox := RabbitMQ.inbox handle
        send := fun message => RabbitMQ.send config.mailboxes.scheduler run "scheduler" message
        observe := ⟨records, pure #[]⟩
        blobs := S3.storage config.blobs : Worker.Ports IO }
      let scheduler : SchedulerPorts IO := {
        inbox := RabbitMQ.inbox schedulerHandle
        localDb := LocalDb.store conn run
        send := config.mailboxes.sendWorker run }
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

private def stagedMailbox (config : Config) (run : String) (index : Nat) (publish : Bool) : IO Unit := do
  let brokers := #[config.mailboxes.scheduler] ++ config.mailboxes.workers.map (·.broker)
  let some broker := brokers[index]? | throw (IO.userError "Invalid broker index")
  let handle ← RabbitMQ.openMailbox broker run "broker-restart" (!publish)
  try
    if publish then handle.send (WorkerMessage.acknowledged 73)
    else
      let inbox : Mailbox IO WorkerMessage := RabbitMQ.inbox handle
      inbox.acknowledge (← receiveAcknowledged handle 73)
      handle.delete
  finally handle.close

def main (args : List String) : IO UInt32 := do
  try
    let path := args.headD "/etc/lean-cloud/config.json"
    let config ← Config.load path
    match args.drop 1 with
    | ["mailbox-seed", run, index] =>
      let some index := index.toNat? | throw (IO.userError "Invalid broker index")
      stagedMailbox config run index true
      return 0
    | ["mailbox-check", run, index] =>
      let some index := index.toNat? | throw (IO.userError "Invalid broker index")
      stagedMailbox config run index false
      return 0
    | [] => pure ()
    | _ => throw (IO.userError "Invalid integration test arguments")
    let runPrefix := s!"properties-{← IO.Process.getPID}-{← IO.monoMsNow}"
    checkAdapters config runPrefix
    checkPrograms config runPrefix
    checkIsolation config runPrefix
    for broker in #[config.mailboxes.scheduler] ++ config.mailboxes.workers.map (·.broker) do
      checkMailboxes broker runPrefix
    for seed in [:16] do
      let tree := (generate 3 seed).1
      try compareProgram config s!"{runPrefix}-{seed}" tree (seed % 7)
      catch error => throw (IO.userError s!"seed={seed}, program={reprStr tree}\n{error}")
    IO.println "Real adapters: independent broker isolation, durable redelivery on every broker, immutable writes, concurrent creation, blob integrity, SQLite recovery, and 16 differential programs passed."
    return 0
  catch error => IO.eprintln error.toString; return 1
