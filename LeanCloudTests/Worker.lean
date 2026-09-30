import LeanCloudTests.Recovery

namespace LeanCloudTests.WorkerTests
open Lean LeanCloud

private abbrev Receipt := LeaseQueueModel.Receipt

/-- Connection tests reuse SimulationBackend's actual primitive operations.
This fixture is not a network backend or a real queue implementation. -/
private structure Fixture where
  durable : IO.Ref SimulationBackend.Durable
  events : IO.Ref (Array String)
  userBlobs : Ref

private def fixture (initial := SimulationBackend.initial) : IO Fixture :=
  return ⟨← IO.mkRef initial, ← IO.mkRef #[], ← IO.mkRef LeanCloudTests.initial⟩

private def simulated (f : Fixture) (action : SimulationBackend.M α) : IO α := do
  let (value, durable) ← SimTest.finish action (← f.durable.get)
  f.durable.set durable
  return value

private def rawDb (f : Fixture) : Db Unit IO where
  get key state := simulated f (SimulationBackend.rawDb.get key state)
  put key value state := simulated f (SimulationBackend.rawDb.put key value state)

private def transport (f : Fixture) (failAck : Bool) : LeaseQueue Unit IO Receipt where
  enqueue location state := simulated f ((SimulationBackend.transport 100).enqueue location state)
  dequeue state := simulated f ((SimulationBackend.transport 100).dequeue state)
  acknowledge receipt state := do
    f.events.modify (·.push "ack")
    if failAck then throw (IO.userError "ack unavailable")
    simulated f ((SimulationBackend.transport 100).acknowledge receipt state)

private def blobs (f : Fixture) : BlobStorage Unit IO where
  putBlob bytes state := do
    let (result, _) ← (blobStorage.putBlob bytes).run f.userBlobs
    return (result, state)
  readBlob ref state := do
    let (result, _) ← (blobStorage.readBlob ref).run f.userBlobs
    return (result, state)
  resolveBlob name state := do
    let (result, _) ← (blobStorage.resolveBlob name).run f.userBlobs
    return (result, state)

private def config : WorkerConfig String String String :=
  ⟨"model://db/run-1", "model://queue/run-1", "model://blobs/shared"⟩

private def connection (f : Fixture) (name requested expected : String) (service : α)
    (failOpen failClose : Option String) : IO (Worker.Connection α) := do
  assertEq requested expected "Connector received the wrong configuration"
  f.events.modify (·.push s!"open/{name}")
  if failOpen == some name then throw (IO.userError s!"open failed/{name}")
  return ⟨service, do
    f.events.modify (·.push s!"close/{name}")
    if failClose == some name then throw (IO.userError s!"close failed/{name}")⟩

private def connectors (f : Fixture) (failOpen : Option String := none)
    (failClose : Option String := none) (failAck := false) :
    Worker.Connectors String String String Receipt where
  db setting := connection f "db" setting config.db (rawDb f) failOpen failClose
  queue setting := connection f "queue" setting config.queue (transport f failAck) failOpen failClose
  blobs setting := connection f "blobs" setting config.blobs (blobs f) failOpen failClose

private def ioError (action : IO α) : IO (Option String) := do
  try
    let _ ← action
    return none
  catch error => return some error.toString

private def closed (f : Fixture) : IO Unit := do
  assertEq ((← f.events.get).filter ("close/".isPrefixOf ·))
    #["close/queue", "close/blobs", "close/db"] "Connections were not all released"

private def stored (f : Fixture) : IO (Option Exit) := do
  let some value := (← f.durable.get).records.lookup Worker.completionKey | return none
  match fromJson? value with
  | .ok outcome => return some outcome
  | .error error => throw (IO.userError error)

def cases : Array TestCase := #[
  ⟨"worker/configuration", IO.FS.withTempFile fun handle path => do
    handle.putStr (toJson config).compress
    handle.flush
    let loaded : WorkerConfig String String String ← WorkerConfig.load path
    assertEq (toJson loaded) (toJson config)⟩,
  ⟨"worker/configuration-errors", do
    for contents in ["{invalid-secret", "{\"db\":\"secret\",\"queue\":42,\"blobs\":\"shared\"}"] do
      IO.FS.withTempFile fun handle path => do
        handle.putStr contents
        handle.flush
        let error ← ioError (WorkerConfig.load (d := String) (q := String) (b := String) path)
        assertEq error (some "Invalid worker configuration")⟩,
  ⟨"worker/partial-connection-cleanup", do
    for (service, expected) in [
      ("db", #["open/db"]),
      ("blobs", #["open/db", "open/blobs", "close/db"]),
      ("queue", #["open/db", "open/blobs", "open/queue", "close/blobs", "close/db"])] do
      let f ← fixture
      let error ← ioError (Worker.run (connectors f (some service)) config 100
        (fun n : Nat => pure n) 42)
      assertEq error (some s!"open failed/{service}")
      assertEq (← f.events.get) expected
      assertEq (← f.durable.get) SimulationBackend.initial⟩,
  ⟨"worker/close-failure-still-closes-others", do
    let f ← fixture
    let error ← ioError (Worker.run (connectors f (failClose := some "queue")) config 100
      (fun n : Nat => pure n) 42)
    assertEq error (some "close failed/queue")
    assertEq (← stored f) (some (.success (toJson (42 : Nat))))
    closed f⟩,
  ⟨"worker/startup-does-not-submit", do
    let f ← fixture {}
    let result ← Worker.run (connectors f) config 4 (fun n : Nat => pure n) 42
    assertOutcome result (.error ⟨.protocol, "Interpreter fuel exhausted"⟩)
    assertEq (← f.durable.get) {}
    closed f⟩,
  ⟨"worker/failure-is-durable", do
    let f ← fixture
    let program (_ : Unit) : Cloud IO Nat := Cloud.fail "workflow failed"
    let result ← Worker.run (connectors f) config 100 program ()
    let error : CloudError := ⟨.application, "workflow failed"⟩
    assertOutcome result (.error error)
    assertEq (← stored f) (some (.failure error))
    closed f⟩,
  ⟨"worker/io-failure-is-not-completion", do
    let f ← fixture
    let program (_ : Unit) : Cloud IO Nat := Cloud.exec fun _ =>
      throw (IO.userError "exec unavailable")
    assertEq (← ioError (Worker.run (connectors f) config 100 program ()))
      (some "exec unavailable")
    assertEq (← stored f) none
    assertEq ((← f.events.get).filter (· == "ack")) #[]
    let retained := (← f.durable.get).transport.messages.any Option.isSome
    assertTrue retained "IO failure lost the delivered work"
    closed f⟩,
  ⟨"worker/completed-restart-after-ack-failure", do
    let f ← fixture
    let program (n : Nat) : Cloud IO Nat := pure n
    assertEq (← ioError (Worker.run (connectors f (failAck := true)) config 100 program 42))
      (some "ack unavailable")
    assertEq (← stored f) (some (.success (toJson (42 : Nat))))
    closed f
    let saved ← f.durable.get
    f.events.set #[]
    let result ← Worker.run (connectors f) config 100 program 42
    assertOutcome result (.ok 42)
    assertEq (← f.durable.get) saved "Completed restart changed durable state"
    assertEq ((← f.events.get).filter (· == "ack")) #[]
    closed f⟩,
  ⟨"worker/malformed-completion", do
    let f ← fixture { records := [(Worker.completionKey, Json.null)] }
    assertEq (← ioError (Worker.run (connectors f) config 100 (fun n : Nat => pure n) 42))
      (some "Invalid workflow completion record")
    closed f⟩,
  ⟨"worker/blob-connections", do
    let f ← fixture
    let program (_ : Unit) : Cloud IO BlobRef := cloud {
      let text ← CloudBlob.readTextByName "seed"
      CloudBlob.putText (text ++ " processed")
    }
    let .ok ref ← Worker.run (connectors f) config 100 program ()
      | throw (IO.userError "Blob workflow failed")
    let (bytes, _) ← (blobStorage.readBlob ref).run f.userBlobs
    assertOutcome (bytes.map (·.data)) (.ok "seed: λ 🌍 processed".toUTF8.data)
    closed f⟩
]

/-- The same generated pure program goes through direct + SimM, replay + SimM,
and the IO worker startup path backed by those same simulated primitives. -/
def generatedCases : Array TestCase := (Array.range 32).map fun seed =>
  ⟨s!"worker/generated/{seed}", do
    let tree := (generate 4 (seed + 1)).1
    let input := seed % 13
    let simProgram : Nat → Cloud SimulationBackend.M Nat := RecoveryTests.lowerPure tree
    let (direct, untouched) ← SimTest.finish
      ((DirectInterpreter.interpret SimulationBackend.noBlobs simProgram input).run ⟨(), none⟩)
      SimulationBackend.initial
    assertEq untouched SimulationBackend.initial "Direct evaluation touched durable state"
    let (replay, durable) ← SimTest.finish
      (SimulationBackend.attempt 10000 100 simProgram input) SimulationBackend.initial
    assertOutcome replay.1 direct.1
    let f ← fixture
    let actual ← Worker.run (connectors f) config 10000 (RecoveryTests.lowerPure tree) input
    assertOutcome actual direct.1
    assertEq (← stored f) durable.completed
    assertEq ((← f.durable.get).records.filter (·.1 != Worker.completionKey)) durable.records
    closed f⟩

end LeanCloudTests.WorkerTests
