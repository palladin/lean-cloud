import LeanCloudTests.ConsoleSupport
import LeanCloudTests.PoolWorkload

namespace LeanCloudTests.ConsoleRuntime
open Lean LeanCloud LeanCloudCli

private def chaosEvent (ctx : Context) (kind : String) (fields : List (String × Json) := []) : Cli Unit := do
  let event := Json.mkObj (("timeMs", toJson (← request .now)) :: ("event", toJson kind) :: fields)
  request (.appendFile (ctx.home / "chaos-events.jsonl") (event.compress ++ "\n"))
  printLine (Json.mkObj (("event", toJson kind) :: fields.filter (·.1 != "runs"))).compress
  request .flush

private def healthy (ctx : Context) (role : String) : Cli Unit := do
  let deadline := (← request .now) + 90000
  repeat
    let health ← docker #["exec", ctx.node role, "cloud-node", "health"] false
    if health.exitCode == 0 then return
    require ((← request .now) < deadline) s!"{role} did not recover HTTP and its actor"
    request (.sleep 250)

private def states (ctx : Context) (runs : Array Run) : Cli (Array Scheduler.State) :=
  runs.mapM ctx.scheduler

/-- Wait for reported assignments rather than injecting faults into an idle pool.
The pre-fault snapshot is evidence of activity, not an exact instruction boundary. -/
private def busy (ctx : Context) (runs : Array Run) (completedBranches : Nat) (overlap : Bool) :
    Cli (Array Scheduler.State × Array String) := do
  let deadline := (← request .now) + 60000
  repeat
    let snapshots ← states ctx runs
    let workers := snapshots.foldl (fun workers state => state.jobs.foldl (fun workers job =>
      match job.status with
      | .running worker _ _ => if workers.contains worker then workers else workers.push worker
      | _ => workers) workers) (#[] : Array String)
    let active := snapshots.filter (!·.finished)
    let completed := snapshots.foldl (fun n state => n + (state.jobs.filter (·.status == .done)).size) 0
    if !workers.isEmpty && completed ≥ completedBranches &&
        (!overlap || (active.size ≥ 2 && active.all (·.jobs.size > 1))) then
      return (snapshots, workers)
    require (!active.isEmpty) "Chaos missed active work: all workflows already finished"
    require ((← request .now) < deadline) "No active assignments available for fault injection"
    request (.sleep 100)

private def settled (ctx : Context) (runs : Array Run) (deadline : Nat) : Cli Unit := do
  repeat
    let snapshots ← states ctx runs
    if snapshots.all (·.finished) then return
    require ((← request .now) < deadline) "Durable results exist but scheduler did not finish"
    request (.sleep 250)

private def crashNode (ctx : Context) (role : String) : Cli Unit := do
  let before ← docker #["inspect", "--format", "{{.State.StartedAt}}", ctx.node role]
  discard <| docker #["kill", "--signal", "KILL", ctx.node role]
  let killed ← docker #["inspect", "--format", "{{.State.Running}} {{.State.ExitCode}}", ctx.node role]
  require (killed.stdout.trimAscii.toString == "false 137") s!"{role} was not observed exiting from SIGKILL"
  chaosEvent ctx "killed" [("node", toJson role), ("exitCode", toJson (137 : Nat))]
  discard <| docker #["start", ctx.node role]
  healthy ctx role
  let after ← docker #["inspect", "--format", "{{.State.StartedAt}}", ctx.node role]
  require (after.stdout != before.stdout) s!"{role} did not restart"
  chaosEvent ctx "restarted" [("node", toJson role)]

private def connection (ctx : Context) (role : String) (connected : Bool) : Cli Unit := do
  let network := ctx.project ++ "_default"
  let deadline := (← request .now) + 60000
  repeat
    let output ← docker #["inspect", "--format", "{{json .NetworkSettings.Networks}}", ctx.node role]
    let networks ← liftExcept (Json.parse output.stdout)
    let endpoint := (networks.getObjVal? network).toOption
    if connected then
      -- Transport errors can put the node in Docker's restart loop. An endpoint
      -- may be registered before its network sandbox has been recreated.
      if endpoint.any (fun value => (value.getObjValAs? String "IPAddress").toOption.any (!·.isEmpty)) then break
      if endpoint.isNone then
        discard <| docker #["network", "connect", "--alias", role ++ "-mailbox", network, ctx.node role] false
    else
      if endpoint.isNone then break
      discard <| docker #["network", "disconnect", network, ctx.node role] false
    require ((← request .now) < deadline) s!"{role}: network change was not applied"
    request (.sleep 200)
  chaosEvent ctx (if connected then "connected" else "disconnected") [("node", toJson role)]

private structure Interrupted where
  run : Run
  worker : String
  assignment : Assignment

private def owns (state : Scheduler.State) (old : Interrupted) : Bool :=
  state.jobs.any fun job => job.branch == old.assignment.branch &&
    (Scheduler.Internal.assignedTo old.worker job).any (·.attempt == old.assignment.attempt)

/-- Deliver an explicitly synthetic late failure and heartbeat through the real
HTTP inbox. If the old attempt is still accepted, this poisons the run. Repeating
the messages also checks duplicate delivery, including after final completion. -/
private def lateMessages (ctx : Context) (old : Interrupted) : Cli Unit := do
  let endpoint ← readJson (α := Json) (ctx.home / "api.json")
  let port ← docker #["port", ctx.node "scheduler", "8080/tcp"]
  let url := "http://" ++ port.stdout.trimAscii.toString ++ "/mailbox"
  let token ← liftExcept (endpoint.getObjValAs? String "token")
  let report : Report := ⟨old.worker, old.assignment.attempt,
    .error ⟨.protocol, "Synthetic late report from disconnected worker"⟩, #[]⟩
  for message in #[Pool.Message.renew old.run.id old.worker old.assignment.attempt,
      .report old.run.id report, .report old.run.id report] do
    let envelope := Json.mkObj [("event", Json.mkObj [("message", toJson message)])]
    let body := Json.mkObj [("queue", toJson (toJson ("pool-v1", "scheduler")).compress),
      ("session", toJson ""), ("operation", Json.mkObj [
        ("send", Json.mkObj [("payload", toJson envelope.compress)])])]
    let response ← request (.httpPost url token body.compress)
    let accepted : Except String Json ← liftExcept (Json.parse response >>= fromJson?)
    discard <| liftExcept accepted
  -- Status is enqueued after the injected messages, so it is a processing barrier.
  let state ← ctx.scheduler old.run
  require state.error.isNone "An expired attempt installed a terminal failure"
  require (!owns state old) "A late heartbeat revived the disconnected attempt"
  chaosEvent ctx "stale-messages-rejected" [("run", toJson old.run.id),
    ("worker", toJson old.worker), ("attempt", toJson old.assignment.attempt)]

private def completedCount (snapshots : Array Scheduler.State) : Nat :=
  snapshots.foldl (fun n state => n + (state.jobs.filter (·.status == .done)).size) 0

/-- Disconnect a busy worker, then capture the assignment still owned by it.
It may have advanced since the initial observation. If it has no outstanding
work, reconnect and choose again instead of claiming to test expiry. -/
private def isolateWorker (ctx : Context) (runs : Array Run) : Cli (Interrupted × Nat) := do
  for _ in [:10] do
    let (_, workers) ← busy ctx runs 0 true
    let worker := workers[0]!
    connection ctx worker false
    let captured ← observing do
      let after ← states ctx runs
      let some (run, assignment) := (runs.zip after).findSome? fun (run, state) =>
          (state.jobs.findSome? (Scheduler.Internal.assignedTo worker)).map (run, ·)
        | return none
      chaosEvent ctx "worker-isolated" [("run", toJson run.id), ("worker", toJson worker),
        ("assignment", toJson assignment), ("runs", toJson after)]
      return some (⟨run, worker, assignment⟩, completedCount after)
    match captured with
    | .ok (some result) => return result
    | _ =>
      connection ctx worker true
      healthy ctx worker
      match captured with
      | .error error => throw error
      | _ => chaosEvent ctx "missed-assignment" [("worker", toJson worker)]
  throw "Could not disconnect an active assignment before its report arrived"

/-- Scheduler observations retain brief assignments which might complete between
polls. Require positive evidence of reassignment; final correctness still comes
from durable results, not telemetry. Missing observations fail this test. -/
private def awaitReplacement (ctx : Context) (runs : Array Run) (old : Interrupted)
    (before : Nat) (lease : Nat) : Cli Unit := do
  let deadline := (← request .now) + lease + 60000
  repeat
    let snapshots ← states ctx runs
    let output ← docker #["logs", "--tail", "2000", ctx.node "scheduler"]
    let replacement := (output.stdout ++ output.stderr).splitOn "\n" |>.findSome? fun line => do
      let step ← LeanCloudCli.Trace.parse line
      guard (step.event.run == old.run.id)
      let job ← step.job
      guard (job.branch == old.assignment.branch)
      let .running worker attempt := job.status | none
      guard (worker != old.worker && attempt > old.assignment.attempt)
      return (worker, attempt)
    if let some (worker, attempt) := replacement then
      if completedCount snapshots > before then
        chaosEvent ctx "reassigned" [("run", toJson old.run.id), ("from", toJson old.worker),
          ("to", toJson worker), ("oldAttempt", toJson old.assignment.attempt),
          ("attempt", toJson attempt), ("branch", toJson old.assignment.branch),
          ("completedBefore", toJson before), ("completedAfter", toJson (completedCount snapshots))]
        return
    require ((← request .now) < deadline) "Disconnected work was not reassigned while healthy workers progressed"
    request (.sleep 500)

private def networkFaults (ctx : Context) (runs : Array Run) : Cli Interrupted := do
  let config ← readJson (α := Json) (← ctx.configFile)
  let lease ← liftExcept (config.getObjVal? "scheduler" >>= (·.getObjValAs? Nat "assignmentMs"))
  let before ← docker #["inspect", "--format", "{{.State.StartedAt}}", ctx.node "scheduler"]
  let (old, completed) ← isolateWorker ctx runs
  try
    awaitReplacement ctx runs old completed lease
    lateMessages ctx old
    let after ← docker #["inspect", "--format", "{{.State.StartedAt}}", ctx.node "scheduler"]
    require (before.stdout == after.stdout) "An isolated worker caused the scheduler to restart"
  finally connection ctx old.worker true
  healthy ctx old.worker
  -- Do not stop or restart the scheduler explicitly: only remove its network.
  -- Runtime transport failures may naturally trigger Docker's restart policy.
  let (snapshots, _) ← busy ctx runs 0 false
  chaosEvent ctx "scheduler-isolation" [("durationMs", toJson (lease + 5000)), ("runs", toJson snapshots)]
  connection ctx "scheduler" false
  try request (.sleep (lease + 5000).toUInt32)
  finally connection ctx "scheduler" true
  healthy ctx "scheduler"
  -- Health confirms only the HTTP server. Require new completed branches after
  -- reconnecting, before any explicit crash/restart could hide failed recovery.
  let deadline := (← request .now) + 90000
  let mut baseline : Option Nat := none
  repeat
    if let .ok current ← observing (states ctx runs) then
      let completed := completedCount current
      match baseline with
      | none => baseline := some completed
      | some before =>
        if completed > before then
          chaosEvent ctx "network-recovered" [("completedBefore", toJson before), ("completedAfter", toJson completed)]
          break
    require ((← request .now) < deadline) "Scheduler did not recover after reconnecting"
    request (.sleep 500)
  return old

private def chaosFixture (owner : Context) : Cli Context := do
  let directory := owner.home / "application"
  Project.init owner directory.toString (some owner.root.toString)
  let ctx : Context := ⟨directory, owner.project⟩
  isolate ctx
  -- The test fixture is compiled into a normal application, not the demo registry.
  request (.createDir (directory / "ChaosFixture"))
  request (.appendFile (directory / "lakefile.lean") "\nlean_lib ChaosFixture\n")
  request (.writeFile (directory / "ChaosFixture/GeneratedProgram.lean") (include_str "GeneratedProgram.lean"))
  request (.writeFile (directory / "ChaosFixture/PoolWorkload.lean")
    ((include_str "PoolWorkload.lean").replace "import LeanCloudTests.GeneratedProgram" "import ChaosFixture.GeneratedProgram"))
  request (.writeFile (directory / "Main.lean") (include_str "Fixtures/PoolChaosMain.lean.in"))
  return ctx

/-- Generate the exact test application for a separately timed CI image build.
The subsequent suite still executes the normal deploy command. -/
def prepareChaosImage : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let ctx ← chaosFixture ⟨root, "ci-chaos"⟩
  Project.prepare ctx

/-- Run the generated pure workloads through the ordinary CLI deployment,
registry, combined HTTP/SQLite nodes, shared pool and S3 record store. -/
def poolChaos (seed : Nat := 1) : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let ctx ← chaosFixture ⟨root, s!"lean-cloud-pool-chaos-test-{← request .pid}"⟩
  let inputs := PoolWorkload.inputs seed
  let faults := PoolWorkload.plan seed
  saveJson (ctx.home / "chaos-plan.json") (Json.mkObj [
    ("generator", toJson "pool-chaos/v2"), ("seed", toJson seed), ("faults", toJson faults),
    ("networkFaults", toJson #["busy-worker-until-reassigned", "scheduler-beyond-assignment-lease"]),
    ("programs", toJson (inputs.map fun input => Json.mkObj [
      ("input", toJson input), ("tree", toJson (reprStr (PoolWorkload.tree input))),
      ("expected", toJson (PoolWorkload.expected input))]))])
  printLine s!"Pool chaos seed={seed}; artifacts: {ctx.home}"
  try
    ctx.deploy (workers := some 3)
    let identities ← poolNodes ctx
    let mut runs := #[]
    for i in [:inputs.size] do
      let file := ctx.home / s!"input-{i}.json"
      saveJson file inputs[i]!
      let id := s!"generated-{i}"
      ctx.launch "generated" (some file.toString) (some id)
      runs := runs.push (← ctx.loadRun id)
    let interrupted ← networkFaults ctx runs
    for i in [:faults.size] do
      let fault := faults[i]!
      request (.sleep fault.delayMs.toUInt32)
      let (snapshots, workers) ← busy ctx runs fault.completedBranches (i == 0)
      let role := if fault.scheduler then "scheduler" else workers[fault.workerOffset % workers.size]!
      chaosEvent ctx "inject" [("index", toJson i), ("node", toJson role),
        ("runs", toJson (runs.zip snapshots |>.map fun (run, state) =>
          Json.mkObj [("id", toJson run.id), ("state", toJson state)]))]
      crashNode ctx role
    chaosEvent ctx "faults-stopped"
    let deadline := (← request .now) + 300000
    for (run, input) in runs.zip inputs do
      let actual ← awaitOutcome ctx run deadline
      let expected := PoolWorkload.expected input
      chaosEvent ctx "result" [("run", toJson run.id), ("actual", toJson actual), ("expected", toJson expected)]
      require (actual == expected) s!"seed={seed}, run={run.id}: direct/replay mismatch"
    -- Wait for the scheduler to consume the final reports as well as the root writes.
    settled ctx runs deadline
    lateMessages ctx interrupted
    -- Completed outcomes must survive another scheduler restart and stale delivery.
    crashNode ctx "scheduler"
    for (run, input) in runs.zip inputs do
      require ((← awaitOutcome ctx run deadline) == PoolWorkload.expected input)
        s!"Completed result changed after restart: {run.id}"
    settled ctx runs deadline
    require ((← poolNodes ctx) == identities) "Recovery replaced deployed nodes"
    chaosEvent ctx "passed" [("seed", toJson seed), ("crashes", toJson faults.size), ("partitions", toJson (2 : Nat))]
    printLine "Pool chaos passed: network partitions, reassignment, stale reports, scheduler/worker crashes, direct outcomes, and durable recovery."
  catch error =>
    discard <| observing (chaosEvent ctx "failed" [("error", toJson error)])
    discard <| observing (captureFailure ctx)
    throw s!"Pool chaos seed={seed}: {error}\nArtifacts: {ctx.home}"
  finally cleanup ctx

end LeanCloudTests.ConsoleRuntime
