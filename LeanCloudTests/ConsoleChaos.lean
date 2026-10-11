import LeanCloudTests.ConsoleFixture

/-! Fault injection belongs to the deployment test harness. Workflow operations
still use the same HTTP client as an ordinary user. -/
namespace LeanCloudTests.ConsoleRuntime
open Lean LeanCloud LeanCloudCli

private def event (f : Fixture) (name : String) (fields : List (String × Json) := []) : IO Unit := do
  let value := Json.mkObj (("event", toJson name) :: ("timeMs", toJson (← IO.monoMsNow)) :: fields)
  IO.FS.withFile (f.directory / "chaos-events.jsonl") .append fun file => file.putStrLn value.compress
  IO.println value.compress
  (← IO.getStdout).flush

private def snapshots (f : Fixture) (runs : Array Run) : IO (Array Scheduler.Snapshot) :=
  cli (runs.mapM fun run => (·.toSnapshot) <$> f.context.observation run)

private def busy (f : Fixture) (runs : Array Run) (completed := 0) (overlap := false) :
    IO (Array Scheduler.Snapshot × Array String) := do
  -- A restarted scheduler may first wait for the durable inbox's 60s lease.
  let deadline := (← IO.monoMsNow) + 120000
  repeat
    let states ← snapshots f runs
    let workers := states.foldl (fun workers state => state.jobs.foldl (fun workers job =>
      match job.status with
      | .running worker _ _ => if workers.contains worker then workers else workers.push worker
      | _ => workers) workers) (#[] : Array String)
    let doneCount := states.foldl (fun n state => n + (state.jobs.filter (·.status == .done)).size) 0
    let active := states.filter (!·.finished)
    if !workers.isEmpty && doneCount ≥ completed &&
        (!overlap || (active.size ≥ 2 && active.all (·.jobs.size > 1))) then return (states, workers)
    assertTrue (!active.isEmpty) "Fault missed active work"
    assertTrue ((← IO.monoMsNow) < deadline) "No active assignments for fault injection"
    IO.sleep 100

private def node (f : Fixture) (role : String) : IO String := do
  let id ← f.compose #["ps", "-a", "-q", role]
  assertTrue (!id.isEmpty) s!"Missing {role}"
  return id

private def healthy (f : Fixture) (role : String) : IO Unit := do
  let id ← node f role
  let deadline := (← IO.monoMsNow) + 90000
  repeat
    let result ← IO.Process.output { cmd := "docker", args := #["exec", id, "cloud-node", "health"] }
    if result.exitCode == 0 then return
    assertTrue ((← IO.monoMsNow) < deadline) s!"{role} did not recover"
    IO.sleep 250

private def network (f : Fixture) (role : String) (connected : Bool) : IO Unit := do
  let id ← node f role
  let network := f.context.project ++ "_default"
  let alias := if role == "blobs" then role else role ++ "-mailbox"
  let deadline := (← IO.monoMsNow) + 60000
  repeat
    let text ← external "docker" #["inspect", "--format", "{{json .NetworkSettings.Networks}}", id]
    let json ← unwrap (Json.parse text)
    let endpoint := (json.getObjVal? network).toOption
    if connected then
      if endpoint.any (fun value => (value.getObjValAs? String "IPAddress").toOption.any (!·.isEmpty)) then break
      if endpoint.isNone then
        discard <| IO.Process.output { cmd := "docker", args := #["network", "connect", "--alias", alias, network, id] }
    else
      if endpoint.isNone then break
      discard <| IO.Process.output { cmd := "docker", args := #["network", "disconnect", network, id] }
    assertTrue ((← IO.monoMsNow) < deadline) s!"{role}: network change failed"
    IO.sleep 200
  if connected && role == "scheduler" then f.refresh
  event f (if connected then "connected" else "disconnected") [("node", toJson role)]

private def crash (f : Fixture) (role : String) : IO Unit := do
  let id ← node f role
  let before ← external "docker" #["inspect", "--format", "{{.State.StartedAt}}", id]
  let mut confirmed := false
  for _ in [:3] do
    let signal ← IO.Process.output { cmd := "docker", args := #["kill", "--signal", "KILL", id] }
    let state ← external "docker" #["inspect", "--format", "{{.State.Running}} {{.State.ExitCode}}", id]
    if signal.exitCode == 0 && state == "false 137" then confirmed := true; break
    discard <| external "docker" #["start", id]
    healthy f role
  assertTrue confirmed s!"{role} was not observed exiting from SIGKILL"
  discard <| external "docker" #["start", id]
  healthy f role
  if role == "scheduler" then f.refresh
  assertTrue ((← external "docker" #["inspect", "--format", "{{.State.StartedAt}}", id]) != before) "Node did not restart"
  event f "SIGKILL-and-restart" [("node", toJson role)]

private def progress (f : Fixture) (runs : Array Run) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 90000
  let mut baseline : Option Nat := none
  repeat
    let current ← try pure (some (← snapshots f runs)) catch _ => pure none
    if let some current := current then
      assertTrue (current.all (·.error.isNone)) "Transport failure became a workflow error"
      let completed := current.foldl (fun n state => n + (state.jobs.filter (·.status == .done)).size) 0
      if baseline.any (· < completed) then return
      if baseline.isNone then baseline := some completed
    assertTrue ((← IO.monoMsNow) < deadline) "No progress after recovery"
    IO.sleep 500

private def readRecords (f : Fixture) (keys : Array (String × Array String)) : IO (Array (String × Array (String × Json))) := do
  -- This diagnostic command is part of the test application, not the cloud CLI.
let output ← IO.Process.output { cmd := "docker", args := #["exec", "-i", ← node f "scheduler",
  "cloud-app", "read-records", "/etc/lean-cloud/config.json"] } (some ((toJson keys).compress ++ "\n"))
assertEq output.exitCode 0 output.stderr
unwrap (Json.parse output.stdout >>= fromJson?)

private def storageFailures (f : Fixture) : IO (Array Nat) := do
  (#["worker1", "worker2", "worker3"]).mapM fun worker => do
    let output ← IO.Process.output { cmd := "docker", args := #["logs", ← node f worker] }
    return ((output.stdout ++ output.stderr).splitOn "S3 transport failed (curl ").length - 1

private def blobOutage (f : Fixture) (runs : Array Run) : IO (Array (String × Array (String × Json))) := do
  let (states, _) ← busy f runs 3 true
  let keys := (runs.zip states).map fun (run, state) =>
    (run.id, state.workers.foldl (fun keys worker => worker.recorded.foldl
      (fun keys key => if keys.contains key then keys else keys.push key) keys) (#[] : Array String))
  assertTrue (keys.all (!·.2.isEmpty)) "Missing confirmed records before blob outage"
  let saved ← readRecords f keys
  discard <| busy f runs 3 true
  let before ← storageFailures f
  network f "blobs" false
  try
    let deadline := (← IO.monoMsNow) + 90000
    repeat
      assertTrue ((← snapshots f runs).all (·.error.isNone)) "Blob outage installed terminal error"
      let failures ← storageFailures f
      if (failures.zip before).all (fun (after, prior) => after > prior) then break
      assertTrue ((← IO.monoMsNow) < deadline) "Blob outage did not exercise every worker"
      IO.sleep 500
  finally network f "blobs" true
  progress f runs
  assertEq (toJson (← readRecords f keys)) (toJson saved) "Confirmed records changed after blob recovery"
  event f "blob-recovery-preserved-records"
  return saved

private structure Interrupted where
  run : Run
  worker : String
  assignment : Assignment

private def assignedTo (worker : String) (job : Scheduler.Job) : Option Assignment := do
  let .running owner attempt _ := job.status | none
  guard (owner == worker)
  return ⟨attempt, job.branch⟩

private def owns (state : Scheduler.Snapshot) (old : Interrupted) : Bool :=
  state.jobs.any fun job => job.branch == old.assignment.branchStart &&
    (assignedTo old.worker job).any (·.attempt == old.assignment.attempt)

private def lateMessages (f : Fixture) (old : Interrupted) : IO Unit := do
  let config ← unwrap (Json.parse (← IO.FS.readFile (f.directory / "config.json")))
  let token ← unwrap (config.getObjVal? "mailboxes" >>= (·.getObjVal? "scheduler") >>= (·.getObjValAs? String "token"))
  let address ← f.compose #["port", "scheduler", "8080"]
  let report : Report := ⟨old.worker, old.assignment.attempt,
    .error ⟨.protocol, "Synthetic stale failure"⟩, #[]⟩
  for message in #[Pool.Message.renew old.run.id old.worker old.assignment.attempt,
      .report old.run.id report, .report old.run.id report] do
    let envelope := Json.mkObj [("event", Json.mkObj [("message", toJson message)])]
    let body := Json.mkObj [("queue", toJson (toJson ("pool-v1", "scheduler")).compress),
      ("session", toJson ""), ("operation", Json.mkObj [("send", Json.mkObj [("payload", toJson envelope.compress)])])]
    let response ← cli (request (.httpPost ("http://" ++ address ++ "/mailbox") token body.compress))
    let result : Except String Json ← unwrap (Json.parse response >>= fromJson?)
    discard <| unwrap result
  let state ← cli ((·.toSnapshot) <$> f.context.observation old.run)
  assertTrue (state.error.isNone && !owns state old) "Late message revived a cancelled assignment"
  event f "stale-messages-rejected"

private def isolateWorker (f : Fixture) (runs : Array Run) : IO Interrupted := do
  for _ in [:10] do
    let (_, workers) ← busy f runs 0 true
    let worker := workers[0]!
    network f worker false
    let states ← snapshots f runs
    if let some (run, assignment) := (runs.zip states).findSome? fun (run, state) =>
        (state.jobs.findSome? (assignedTo worker)).map (run, ·) then
      return ⟨run, worker, assignment⟩
    network f worker true
    healthy f worker
  throw (IO.userError "Could not isolate an active assignment")

private def partitions (f : Fixture) (runs : Array Run) : IO Interrupted := do
  let old ← isolateWorker f runs
  let scheduler ← node f "scheduler"
  let started ← external "docker" #["inspect", "--format", "{{.State.StartedAt}}", scheduler]
  try
    let deadline := (← IO.monoMsNow) + 90000
    repeat
      if !owns (← cli ((·.toSnapshot) <$> f.context.observation old.run)) old then break
      assertTrue ((← IO.monoMsNow) < deadline) "Disconnected assignment did not expire"
      IO.sleep 500
    let observeUntil := (← IO.monoMsNow) + 2000
    repeat
      let state ← cli ((·.toSnapshot) <$> f.context.observation old.run)
      assertTrue (state.error.isNone) "Worker partition installed terminal error"
      assertTrue (!(state.jobs.any fun job => match job.status with | .running .. => true | _ => false))
        "Replacement executed before isolated worker stopped"
      if (← IO.monoMsNow) ≥ observeUntil then break
      IO.sleep 200
    lateMessages f old
    assertEq (← external "docker" #["inspect", "--format", "{{.State.StartedAt}}", scheduler]) started
      "Worker partition restarted the scheduler"
  finally network f old.worker true
  healthy f old.worker
  progress f runs
  discard <| busy f runs
  network f "scheduler" false
  try IO.sleep 35000 finally network f "scheduler" true
  healthy f "scheduler"
  progress f runs
  return old

def chaos (f : Fixture) : IO Unit := do
  let seed := 7
  let inputs := PoolWorkload.inputs seed
  let mut runs := #[]
  for i in [:inputs.size] do
    let file := f.directory / s!"input-{i}.json"
    IO.FS.writeFile file (toJson inputs[i]!).compress
    f.command ["run", "generated", "--input", file.toString, "--id", s!"generated-{i}"]
    runs := runs.push (← cli (f.context.loadRun s!"generated-{i}"))
  let identities ← f.compose #["ps", "-a", "-q"]
  let saved ← blobOutage f runs
  let old ← partitions f runs
  for fault in PoolWorkload.plan seed do
    IO.sleep fault.delayMs.toUInt32
    let (_, workers) ← busy f runs fault.completedBranches
    crash f (if fault.scheduler then "scheduler" else workers[fault.workerOffset % workers.size]!)
  let deadline := (← IO.monoMsNow) + 300000
  for (run, input) in runs.zip inputs do
    assertEq (← cli (awaitOutcome f.context run deadline)) (PoolWorkload.expected input) "Crash recovery diverged from DirectInterpreter"
  repeat
    if (← snapshots f runs).all (·.finished) then break
    assertTrue ((← IO.monoMsNow) < deadline) "Scheduler did not finalize completed runs"
    IO.sleep 250
  lateMessages f old
  crash f "scheduler"
  for (run, input) in runs.zip inputs do
    assertEq (← cli (awaitOutcome f.context run deadline)) (PoolWorkload.expected input) "Completed outcome changed on restart"
  assertEq (toJson (← readRecords f (saved.map fun (id, records) => (id, records.map Prod.fst)))) (toJson saved)
    "Confirmed replay records changed"
  assertEq (← f.compose #["ps", "-a", "-q"]) identities "Recovery replaced deployed nodes"
  event f "passed" [("seed", toJson seed), ("crashes", toJson (7 : Nat)), ("partitions", toJson (3 : Nat))]

end LeanCloudTests.ConsoleRuntime
