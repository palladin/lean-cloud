import LeanCloudRuntime
import LeanCloudTests.Recovery
import LeanCloudTests.BackendAdapterLaws
import LeanCloudTests.BackendContracts
import Tests.PgSchema

open Lean LeanCloud LeanCloudRuntime LeanCloudTests

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def nextDelivery (queue : LeaseQueue Unit IO RabbitMQ.Receipt) :
    Nat → IO (Location × RabbitMQ.Receipt)
  | 0 => throw (IO.userError "Timed out waiting for RabbitMQ delivery")
  | fuel + 1 => do
    let (delivery, _) ← queue.dequeue ()
    match delivery with
    | some result => return result
    | none => nextDelivery queue fuel

private def queueTest (config : Config) (run : String) : IO Unit := do
  let first ← RabbitMQ.acquire config.queue run (create := true)
  try
    first.enqueue Location.root
    let (location, receipt) ← nextDelivery (RabbitMQ.transport first) 40
    assertEq location Location.root
    -- Close without an ack, then recover through an independent connection.
    first.close
    let second ← RabbitMQ.acquire config.queue run
    try
      let (again, current) ← nextDelivery (RabbitMQ.transport second) 40
      assertEq again Location.root
      let (staleAccepted, _) ← (RabbitMQ.transport second).acknowledge receipt ()
      require (!staleAccepted) "Receipt from another connection was accepted"
      let (accepted, _) ← (RabbitMQ.transport second).acknowledge current ()
      require accepted "Current acknowledgement was rejected"
      -- Duplicate messages remain independently acknowledgeable.
      second.enqueue Location.root.next
      second.enqueue Location.root.next
      for _ in [:2] do
        let (next, token) ← nextDelivery (RabbitMQ.transport second) 40
        assertEq next Location.root.next
        require (← ((RabbitMQ.transport second).acknowledge token ()).map Prod.fst)
          "Duplicate delivery acknowledgement failed"
      let (remaining, _) ← (RabbitMQ.transport second).dequeue ()
      require remaining.isNone "Acknowledged message was not removed"
    finally second.close
  finally first.close

private def dbTest (config : Config) (run : String) : IO Unit := withDb config fun conn => do
  Postgres.initializeSchema conn
  let key := "quoted '\n key; SELECT 1"
  let value := Json.arr #[toJson "Unicode λ 🌍", toJson (17 : Nat), Json.null]
  require (← Postgres.put conn run key value) "Initial database write rejected"
  require (← Postgres.put conn run key value) "Repeated database write rejected"
  require (!(← Postgres.put conn run key Json.null)) "Conflicting database write accepted"
  assertEq (← Postgres.get conn run key) (some value)
  assertEq (← Postgres.get conn (run ++ "-other") key) none
  -- Independent connections race for the same immutable key.
  let first ← IO.asTask (withDb config fun other => Postgres.put other run "race" (toJson (1 : Nat))) .dedicated
  let second ← IO.asTask (withDb config fun other => Postgres.put other run "race" (toJson (2 : Nat))) .dedicated
  let left ← IO.ofExcept first.get
  let right ← IO.ofExcept second.get
  require (left != right) "Conflicting concurrent writers did not have exactly one winner"
  assertEq (← Postgres.get conn run "race") (some (toJson (if left then 1 else 2 : Nat)))

private def blobTest (config : Config) (run : String) : IO Unit := do
  S3.initializeBucket config.blobs
  let bytes := ByteArray.mk #[0, 255, 10, 34, 128, 65]
  let ref ← S3.putBytes config.blobs bytes
  assertEq (← S3.putBytes config.blobs bytes) ref
  let read ← (S3.readBytes config.blobs ref).run
  assertOutcome (read.map (·.data)) (.ok bytes.data)
  let name := run ++ "/λ ? #.bin"
  S3.name config.blobs name ref
  assertOutcome (← (S3.resolve config.blobs name).run) (.ok ref)
  assertError (← (S3.readBytes config.blobs { ref with size := ref.size + 1 }).run) .integrity
  assertError (← (S3.resolve config.blobs (run ++ "/absent")).run) .missingBlob

private def generatedTest (config : Config) (run : String) (seed : Nat) : IO Unit := do
  let tree := (generate 4 (seed + 1)).1
  let input := seed % 13
  let program : Nat → Cloud SimulationBackend.M Nat := RecoveryTests.lowerPure tree
  let (direct, untouched) ← SimTest.finish
    ((DirectInterpreter.interpret SimulationBackend.noBlobs program input).run ⟨(), none⟩)
    SimulationBackend.initial
  assertEq untouched SimulationBackend.initial
  let (replay, modeled) ← SimTest.finish (SimulationBackend.attempt 10000 100 program input)
    SimulationBackend.initial
  assertOutcome replay.1 direct.1
  let (common, commonState) ← BackendContracts.runReplay (RecoveryTests.lowerPure tree) input seed
  assertOutcome common direct.1
  assertEq (Backend.Db.view commonState CompletionStore.key) (modeled.completed.map toJson)
  submit config run ⟨"generated-test/v1", toJson (seed, input), "nat/v1"⟩
  let workers ← (Array.range 3).mapM fun _ =>
    IO.asTask (Worker.run (connectors run) config 10000 (RecoveryTests.lowerPure tree) input) .dedicated
  for worker in workers do
    assertOutcome (← IO.ofExcept worker.get) direct.1
  assertEq (← completed config run) modeled.completed
  let repeated ← Worker.run (connectors run) config 10000 (RecoveryTests.lowerPure tree) input
  assertOutcome repeated direct.1

def main (args : List String) : IO UInt32 := do
  try
    let [path, run] := args | throw (IO.userError "Usage: cloud_integration_tests CONFIG UNIQUE-RUN")
    let config : Config ← WorkerConfig.load path
    validateRun run
    withDb config PgSchemaTests.run
    dbTest config (run ++ "-db")
    queueTest config (run ++ "-queue")
    blobTest config run
    for seed in [:4] do
      let isolated := s!"{run}-contract-{seed}"
      withDb config fun conn => do
        let queue ← RabbitMQ.acquire config.queue isolated (create := true)
        try
          BackendAdapterLaws.run (Postgres.db conn isolated) (RabbitMQ.transport queue) seed
        finally queue.close
    for seed in [:32] do
      generatedTest config s!"{run}-pure-{seed}" seed
    IO.println "40/40 real-backend checks passed (including 4 shared-contract sequences and 32 generated differential cases)"
    return 0
  catch error => IO.eprintln error.toString; return 1
