import LeanCloudRuntime
import LeanCloudTests.Generated

open Lean LeanCloud LeanCloudRuntime LeanCloudTests

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

private def checkMailboxes (config : Config) (run : String) : IO Unit := do
  let first ← RabbitMQ.openMailbox config.broker run "durability"
  try
    first.send (WorkerMessage.acknowledged 42)
    discard <| receiveAcknowledged first 42
  finally first.close
  -- Closing without ack must retain the delivery through repeated crashes.
  -- The reference classic queues have no finite delivery limit.
  for _ in [:24] do
    let handle ← RabbitMQ.openMailbox config.broker run "durability"
    try discard <| receiveAcknowledged handle 42
    finally handle.close
  let handle ← RabbitMQ.openMailbox config.broker run "durability"
  try
    let inbox : Mailbox IO WorkerMessage := RabbitMQ.inbox handle
    inbox.acknowledge (← receiveAcknowledged handle 42)
  finally handle.close
  -- A receive on the old consumer can time out while 42 is still in flight.
  -- Reopen it and require the next confirmed message, rather than an empty poll.
  let reopened ← RabbitMQ.openMailbox config.broker run "durability"
  try
    reopened.send (WorkerMessage.acknowledged 99)
    let inbox : Mailbox IO WorkerMessage := RabbitMQ.inbox reopened
    inbox.acknowledge (← receiveAcknowledged reopened 99)
    reopened.delete
  finally reopened.close

/-- Real RabbitMQ, SQLite, and S3 ports run the same actor turns as Sim. -/
private def compareProgram (config : Config) (run : String) (tree : Tree) (input : Nat) : IO Unit := do
  let program (_ : Unit) : Cloud IO Nat := lower tree input
  let expected ← (DirectInterpreter.interpret (S3.storage config.blobs) program ()).run
  IO.FS.withTempFile fun _ path => do
    let conn ← LeanLinq.Sqlite.connect path.toString
    try
      LocalDb.initializeSchema conn
      let schedulerHandle ← RabbitMQ.openMailbox config.broker run "scheduler"
      let handles ← (Array.range 3).mapM fun index =>
        RabbitMQ.openMailbox config.broker run s!"worker.worker-{index}"
      let records := S3.records config.blobs run
      let workers := handles.mapIdx fun index handle => {
        id := s!"worker-{index}"
        inbox := RabbitMQ.inbox handle
        send := fun message => RabbitMQ.send config.broker run "scheduler" message
        observe := ⟨records, pure #[]⟩
        blobs := S3.storage config.blobs : Worker.Ports IO }
      let scheduler : SchedulerPorts IO := {
        inbox := RabbitMQ.inbox schedulerHandle
        localDb := LocalDb.store conn run
        send := fun delivery =>
          RabbitMQ.send config.broker run ("worker." ++ delivery.worker) delivery.message }
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

private def stagedMailbox (config : Config) (run : String) (publish : Bool) : IO Unit := do
  let handle ← RabbitMQ.openMailbox config.broker run "broker-restart" (!publish)
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
    | ["mailbox-seed", run] => stagedMailbox config run true; return 0
    | ["mailbox-check", run] => stagedMailbox config run false; return 0
    | [] => pure ()
    | _ => throw (IO.userError "Invalid integration test arguments")
    let runPrefix := s!"properties-{← IO.Process.getPID}-{← IO.monoMsNow}"
    checkAdapters config runPrefix
    checkMailboxes config runPrefix
    for seed in [:16] do
      let tree := (generate 3 seed).1
      try compareProgram config s!"{runPrefix}-{seed}" tree (seed % 7)
      catch error => throw (IO.userError s!"seed={seed}, program={reprStr tree}\n{error}")
    IO.println "Real adapters: durable RabbitMQ redelivery, immutable writes, concurrent creation, blob integrity, SQLite recovery, and 16 differential programs passed."
    return 0
  catch error => IO.eprintln error.toString; return 1
