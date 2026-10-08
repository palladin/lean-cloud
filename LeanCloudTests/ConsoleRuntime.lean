import LeanCloudTests.ConsolePoolChaos
import LeanCloudCli.IO

namespace LeanCloudTests.ConsoleRuntime
open Lean LeanCloud LeanCloudCli

/-- Execution counts need raw observations, not the compact watch snapshot. -/
private def events (ctx : Context) (run : Run) : Cli (Array ExecutionEvent) := do
  return (LeanCloudCli.Trace.merge #[] (← LeanCloudCli.Trace.collect ctx).steps).filterMap fun step =>
    if step.event.run == run.id && (workerIndex? step.event.worker).isSome then some step.event else none

private def waitFor (ctx : Context) (run : Run) (expected : Nat) : Cli Unit := do
  match ← awaitOutcome ctx run ((← request .now) + 90000) with
  | .success json =>
    let actual ← liftExcept (Codec.decode (α := Nat) json)
    require (actual == expected) "Console run returned a different result"
  | _ => throw "Console run failed"

/-- The HTTP server and actor fail together; SQLite survives on the node volume. -/
private def nodeRecovery (ctx : Context) : Cli Unit := do
  let node := ctx.node "worker1"
  let started ← docker #["inspect", "--format", "{{.State.StartedAt}}", node]
  discard <| docker #["kill", "--signal", "KILL", node]
  discard <| docker #["start", node]
  let deadline := (← request .now) + 90000
  repeat
    let after ← docker #["inspect", "--format", "{{.State.StartedAt}}", node]
    let health ← docker #["exec", node, "cloud-node", "health"] false
    if after.stdout != started.stdout && health.exitCode == 0 then break
    unless (← request .now) < deadline do throw "Node did not recover HTTP and its actor"
    request (.sleep 500)
  discard <| docker #["stop", node]
  let stopped ← docker #["inspect", "--format", "{{.State.ExitCode}}", node]
  require (stopped.stdout.trimAscii.toString != "137") "Node shutdown needed a forced kill"
  ctx.up

def demo : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let ctx : Context := ⟨root, s!"lean-cloud-console-test-{← request .pid}"⟩
  isolate ctx
  printLine s!"Console test project: {ctx.project}"
  try
    ctx.deploy
    let originalNodes ← poolNodes ctx
    nodeRecovery ctx
    require ((← poolNodes ctx) == originalNodes) "Node recovery replaced containers"
    let deployment ← ctx.deployment
    require (deployment.programs.size ≥ 2) "Registry discovery lost an entry"
    let invalid := ctx.home / "invalid.json"
    saveJson invalid (toJson "not an array")
    let rejected ← try
      ctx.launch "sum-squares" (some invalid.toString) (some "invalid")
      pure false
    catch _ => pure true
    require rejected "Invalid input accepted"
    require (!(← request (.exists (ctx.directory "invalid" / "run.json")))) "Invalid input created a run"
    let input := ctx.home / "numbers with spaces.json"
    saveJson input (toJson (#[2, 3, 4] : Array Nat))
    discard (command ctx ["run", "sum-squares", "--input", input.toString, "--id", "first"])
    ctx.launch "sum-squares" none (some "second")
    let first ← ctx.loadRun "first"
    let second ← ctx.loadRun "second"
    waitFor ctx first 29
    waitFor ctx second 55
    require ((← ctx.allRuns).size == 2) "Run catalog mixed or lost runs"
    let duplicate ← try
      ctx.launch "sum-squares" none (some "first")
      pure false
    catch _ => pure true
    require duplicate "Duplicate run id accepted"
    -- Replacing the mutable build tag must leave the first run's image runnable.
    discard <| docker #["tag", "chrislusf/seaweedfs:4.48", ctx.project ++ "-app:build"]
    ctx.resume "first"
    waitFor ctx first 29
    discard <| docker #["tag", deployment.image, ctx.project ++ "-app:build"]
    let observed ← events ctx second
    require (!observed.isEmpty) "Workers emitted no execution observations"
    require (observed.all (·.run == second.id)) "Watch crossed run traces"
    let recorded ← LeanCloudCli.Trace.load ctx second
    require (recorded.steps.any fun step => step.resources.any fun sample =>
      sample.cpuNs.isSome && sample.memory.any (· > 0) && sample.memoryLimit.any (· > 0))
      "Worker resource metrics were not recorded with the trace"
    let nodes ← ctx.nodes
    require (nodes.toList.Pairwise (fun a b => a.name != b.name)) "Node inventory contains duplicate containers"
    let some source := first.program.sources.find? (·.file.endsWith "Demo.lean") | throw "Missing bundled source"
    require (!source.sites.isEmpty) "No source locations bundled"
    discard (command ctx ["inspect", "first"])
    discard (command ctx ["watch", "first", "--once"])
    -- Completed workflows keep using the same deployed nodes.
    require ((← poolNodes ctx) == originalNodes) "Submitting workflows created or replaced nodes"
    waitFor ctx first 29
    ctx.resume "first"
    let some logs := deployment.programs.find? (·.entry == "log-summary/v1")
      | throw "Missing log example"
    let some sampleInput := logs.sampleInput | throw "Missing log example input"
    let inputFile := ctx.home / "logs.json"
    saveJson inputFile (sampleInput.setObjVal! "pauseMs" (toJson (7000 : Nat)))
    ctx.launch "log-summary" (some inputFile.toString) (some "recover")
    let recover ← ctx.loadRun "recover"
    require (← ctx.outcome recover).isNone "Recovery test missed the active run"
    discard <| docker #["kill", ctx.node "worker1", ctx.node "scheduler"]
    -- docker kill is an explicit operator stop; simulate the external restart.
    discard <| docker #["start", ctx.node "worker1", ctx.node "scheduler"]
    request (.sleep 2000)
    discard <| awaitOutcome ctx recover ((← request .now) + 120000)
    require ((← ctx.remote recover "result") == "files=16, errors=24") "Recovery returned a different report"
    -- A single user effect runs longer than the default 30-second assignment
    -- timeout. The persistent worker must renew without reaching a record boundary.
    let longInput := sampleInput.setObjVal! "pauseMs" (toJson (35000 : Nat))
    saveJson inputFile (longInput.setObjVal! "batchSize" (toJson (16 : Nat)))
    ctx.launch "log-summary" (some inputFile.toString) (some "long-computation")
    let longRun ← ctx.loadRun "long-computation"
    discard <| awaitOutcome ctx longRun ((← request .now) + 90000)
    require ((← ctx.remote longRun "result") == "files=16, errors=24") "Long computation failed to commit"
    let observed ← events ctx longRun
    let executions := (observed.filter fun event => event.activity == "execute" && event.operation == "analyze-batch").size
    require (executions == 1) "Healthy long computation was retried"
    saveJson inputFile (sampleInput.setObjVal! "pauseMs" (toJson (7000 : Nat)))
    -- Pause preserves records and withholds new assignments; shared nodes and
    -- other runs keep working. Kill is terminal and can be retried.
    ctx.launch "log-summary" (some inputFile.toString) (some "paused")
    let paused ← ctx.loadRun "paused"
    require (← ctx.outcome paused).isNone "Pause test missed the active run"
    discard (command ctx ["pause", "paused"])
    ctx.pause "paused"
    require ((← poolNodes ctx) == originalNodes) "Pause replaced or stopped shared nodes"
    require ((← ctx.control "paused") == .paused) "Pause intent was not saved"
    require (← ctx.outcome paused).isNone "Pause published a terminal result"
    discard (command ctx ["watch", "paused", "--once"])
    require (!(← LeanCloudCli.Trace.load ctx paused).steps.isEmpty) "Paused run lost its trace"
    require ((← ctx.control "paused") == .paused) "Watching resumed a paused run"
    ctx.launch "sum-squares" none (some "while-paused")
    waitFor ctx (← ctx.loadRun "while-paused") 55
    require (← ctx.outcome paused).isNone "Paused workflow made progress to completion"
    ctx.launch "log-summary" (some inputFile.toString) (some "killed")
    let killed ← ctx.loadRun "killed"
    require (← ctx.outcome killed).isNone "Kill test missed the active run"
    discard (command ctx ["kill", "killed"])
    require ((← poolNodes ctx) == originalNodes) "Kill replaced or stopped shared nodes"
    require ((← awaitOutcome ctx killed ((← request .now) + 120000)) == .cancelled "Killed by user")
      "Worker did not publish cancellation"
    discard (command ctx ["watch", "killed", "--once"])
    let killedTrace ← LeanCloudCli.Trace.load ctx killed
    require (killedTrace.steps.any (·.event.activity == "sealed")) "Killed run lost its worker finalization event"
    ctx.kill "killed"
    require (← observing (ctx.resume "killed")).toOption.isNone "Killed run resumed"
    require ((← poolNodes ctx) == originalNodes) "Pause replaced or stopped shared nodes"
    ctx.resume "paused"
    discard <| awaitOutcome ctx paused ((← request .now) + 120000)
    require ((← ctx.remote paused "result") == "files=16, errors=24") "Pause/resume changed the result"
    ctx.kill "first"
    waitFor ctx first 29
    ctx.launch "log-summary" (some inputFile.toString) (some "shutdown")
    let interrupted ← ctx.loadRun "shutdown"
    require (← ctx.outcome interrupted).isNone "Shutdown test missed the active run"
    discard (command ctx ["down"])
    let actors ← docker #["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project]
    let services ← docker #["ps", "-aq", "--filter", "label=com.docker.compose.project=" ++ ctx.project]
    require (actors.stdout.trimAscii.isEmpty && services.stdout.trimAscii.isEmpty) "Shutdown left containers behind"
    let offlineTrace ← LeanCloudCli.Trace.load ctx killed
    require (offlineTrace.steps.any (·.event.activity == "sealed") && !offlineTrace.warning.isEmpty)
      "Shutdown discarded the last cancellation view"
    require (offlineTrace.steps.any (·.resources.isSome)) "Shutdown lost the last worker metrics"
    discard (command ctx ["watch", "first", "--once"])
    ctx.down
    ctx.up
    discard (poolNodes ctx)
    waitFor ctx first 29
    require ((← ctx.outcome killed) == some (.cancelled "Killed by user")) "Shutdown lost cancellation"
    require (← observing (ctx.resume "killed")).toOption.isNone "Killed run resumed after deployment restart"
    -- Active runs recover automatically when the pool returns; no resume command.
    discard <| awaitOutcome ctx interrupted ((← request .now) + 120000)
    require ((← ctx.remote interrupted "result") == "files=16, errors=24") "Run failed to resume after shutdown"
    printLine "Console tests passed: registry, validation, concurrent runs, image retention, typed results, source events, crash recovery, pause/resume, and terminal kill."
  catch error =>
    discard <| observing (captureFailure ctx)
    throw error
  finally
    cleanup ctx
    printLine s!"Console test catalog retained: {ctx.home}"

/-- Real scale changes during execution, using the same compiled application,
HTTP/SQLite nodes, scheduler state machine, and replay interpreter. -/
def scaling : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let ctx : Context := ⟨root, s!"lean-cloud-scaling-test-{← request .pid}"⟩
  isolate ctx
  printLine s!"Scaling test project: {ctx.project}"
  try
    ctx.deploy (workers := some 1)
    let identities := #[ctx.node "scheduler", ctx.node "worker1"]
    let fingerprint := #["inspect", "--format", "{{.Id}} {{.State.StartedAt}}"] ++ identities
    let before ← docker fingerprint
    let deployment ← ctx.deployment
    let some program := deployment.programs.find? (·.entry == "log-summary/v1") | throw "Missing example"
    let some input := program.sampleInput | throw "Missing example input"
    let file := ctx.home / "scaling.json"
    saveJson file (input.setObjVal! "pauseMs" (toJson (12000 : Nat)))
    ctx.launch "log-summary" (some file.toString) (some "elastic")
    let run ← ctx.loadRun "elastic"
    ctx.scale 4
    discard (poolNodes ctx)
    let deadline := (← request .now) + 20000
    repeat
      let state ← ctx.scheduler run
      if state.jobs.any (fun job => match job.status with
          | .running "worker4" _ _ => true | _ => false) then break
      unless (← request .now) < deadline do throw "New worker did not join the active workflow"
      request (.sleep 200)
    ctx.scale 1
    discard (poolNodes ctx)
    require ((← docker fingerprint).stdout == before.stdout) "Scaling restarted a retained worker or scheduler"
    let trace ← LeanCloudCli.Trace.load ctx (← ctx.loadRun "elastic")
    require (trace.steps.any (fun step => step.event.worker == "worker4" && step.event.activity == "returned"))
      "Removed worker did not finish its assignment before stopping"
    require (!(trace.steps.any (fun step => step.event.activity == "revoked"))) "Graceful scaling revoked work"
    discard <| awaitOutcome ctx run ((← request .now) + 120000)
    require ((← ctx.remote run "result") == "files=16, errors=24") "Scaling changed workflow output"
    ctx.scale 0
    discard (poolNodes ctx)
    ctx.launch "sum-squares" none (some "waiting")
    let waiting ← ctx.loadRun "waiting"
    require (← ctx.outcome waiting).isNone "A zero-worker deployment executed work"
    ctx.scale 2
    discard (poolNodes ctx)
    waitFor ctx waiting 55
    ctx.down
    ctx.up
    discard (poolNodes ctx)
    waitFor ctx waiting 55
    require ((← ctx.deployment).workers == 2) "Restart forgot scaled capacity"
    require ((← LeanCloudCli.Trace.load ctx run).steps.any (·.event.worker == "worker4")) "Retirement lost history"
    discard <| docker #["stop", ctx.node "worker2"]
    ctx.scale 1
    discard (poolNodes ctx)
    printLine "Elastic scaling passed: live grow/drain, stable nodes, zero capacity, rejoin, restart, and retained history."
  catch error =>
    discard <| observing (captureFailure ctx)
    throw error
  finally cleanup ctx

def generatedApp : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let owner : Context := ⟨root, s!"lean-cloud-app-test-{← request .pid}"⟩
  let directory := owner.home / "application-test"
  Project.init owner directory.toString (some root.toString)
  let ctx : Context := ⟨directory, owner.project⟩
  isolate ctx
  try
    -- Exercise an ordinary executable target, not the SDK's demonstration binary.
    let lakefile ← request (.readFile (directory / "lakefile.lean"))
    request (.writeFile (directory / "lakefile.lean") (lakefile.replace "lean_exe cloud_app" "lean_exe user_app"))
    -- Local editing creates a manifest containing host SDK paths. Deployment
    -- must re-resolve that dependency inside Docker without editing the host file.
    let checked ← request (.process "lake" #["-d", directory.toString, "build", "Main"] none)
    require (checked.exitCode == 0) (checked.stdout ++ checked.stderr)
    let manifest ← request (.readFile (directory / "lake-manifest.json"))
    ctx.deploy (some "user_app") (workers := some 2)
    discard (command ctx ["deployments"])
    let (selected, _) ← dispatch owner ["use", ctx.project]
    require (selected.root == ctx.root && selected.project == ctx.project) "Deployment selection lost application context"
    let remembered ← Deployments.initial owner
    require (remembered.root == ctx.root && remembered.project == ctx.project) "Deployment selection did not survive restart"
    discard (command selected ["status"])
    discard (command selected ["doctor"])
    require ((← request (.readFile (directory / "lake-manifest.json"))) == manifest) "Deployment modified the host dependency manifest"
    let deployment ← ctx.deployment
    require (deployment.programs.map (·.entry) == #["application-test/v1"]) "Image did not contain the user's registry"
    require (deployment.workers == 2 && (← Project.load ctx.root).workers == 2) "Generated application forgot worker capacity"
    saveJson (directory / "input.json") (toJson (#[2, 3, 4] : Array Nat))
    ctx.launch "application-test" (some "input.json") (some "custom")
    let custom ← ctx.loadRun "custom"
    waitFor ctx custom 29
    require ((← ctx.remote custom "result") == "29") "Reusable entry point lost the typed result"
    require ((← LeanCloudCli.Trace.load ctx custom).steps.any (·.resources.isSome))
      "Generated node image lost execution traces or recorded metrics"
    ctx.launch "application-test" none (some "sample")
    waitFor ctx (← ctx.loadRun "sample") 55
    ctx.down
    discard (command ctx ["deployments"])
    discard (command ctx ["status"])
    ctx.up
    require ((← ctx.deployment).image == deployment.image) "up replaced the pinned application image"
    discard (command ctx ["doctor"])
    waitFor ctx custom 29
    -- Reproduce redeploying from down with a changed image. Keep one legacy
    -- per-run config and one current run so both result-reader paths execute.
    saveJson (ctx.directory custom.id / "config.json") (← readJson (α := Json) (← ctx.configFile))
    ctx.down
    let network ← docker #["network", "inspect", ctx.project ++ "_default"] false
    require (network.exitCode != 0) "Redeploy test still had its old network"
    let source ← request (.readFile (directory / "Main.lean"))
    request (.writeFile (directory / "Main.lean") (source.replace "version := \"v1\"" "version := \"v2\""))
    ctx.deploy
    let updated ← ctx.deployment
    require (updated.image != deployment.image) "Redeploy did not build a changed image"
    require (updated.programs.map (·.entry) == #["application-test/v2"]) "Redeploy lost the new registry"
    waitFor ctx custom 29
    waitFor ctx (← ctx.loadRun "sample") 55
    ctx.launch "application-test" none (some "updated")
    waitFor ctx (← ctx.loadRun "updated") 55
    discard (poolNodes ctx)
    printLine "Standalone app tests passed: generated source, deployment catalog, selection, status, doctor, up without rebuilding, relative input, and typed results."
    printLine "Redeploy from down passed: changed image, missing network, legacy/current result checks, and preserved completed runs."
  finally
    cleanup ctx
    printLine s!"Standalone app retained: {directory}"

/-- Invoke the shipped executable through its entry point and argument parser.
Only the environment is isolated; Docker, HTTP, SQLite, and blob storage are real. -/
private def cliCommand (ctx : Context) (args : Array String) (check := true) : Cli ProcessOutput := do
  let executable := ctx.root / ".lake/build/bin/lean_cloud"
  require (← request (.exists executable)) "Build lean_cloud before running the CLI lifecycle test"
  let logs := ctx.root / ".lean-cloud" / s!"cli-command-logs-{← request .pid}"
  request (.createDir logs)
  let log := logs / s!"{← request .now}-{args[0]?.getD "command"}.log"
  printLine s!"CLI: {String.intercalate " " args.toList}"
  let output ← request (.process "env" (#[
    "LEAN_CLOUD_PROJECT=" ++ ctx.project,
    "LEAN_CLOUD_HOME=" ++ (← Deployments.home).toString,
    "NO_COLOR=1", executable.toString] ++ args) none)
  request (.writeFile log (output.stdout ++ output.stderr))
  require (!check || output.exitCode == 0)
    s!"CLI failed (exit {output.exitCode}): {output.stdout}{output.stderr}\nLog: {log}"
  return output

/-- Reproduce the user's command sequence from a saved, stopped RabbitMQ
deployment, then execute and restart a workflow on a fresh HTTP/SQLite pool. -/
def commandLifecycle : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let ctx : Context := ⟨root, s!"lean-cloud-command-test-{← request .pid}"⟩
  isolate ctx
  let source ← request (.readFile (root / "LeanCloud.lean"))
  let defaults ← request (.readFile (root / "deploy/config.json"))
  let retired := ctx.project ++ "_worker7-mailbox-data"
  try
    -- Persist the schema used by old deployments, including history and a
    -- retired worker volume. No old broker needs to be running for this failure.
    request (.createDir (Project.assets ctx))
    let legacy := Project.defaultConfig.setObjVal! "mailboxes" (Json.mkObj [
      ("scheduler", Json.mkObj [("host", toJson "scheduler-mailbox"), ("port", toJson (5672 : Nat))]),
      ("workers", toJson #[Json.mkObj [("worker", toJson "worker1"), ("broker", Json.mkObj [])]])])
    saveJson (Project.assets ctx / "config.json") legacy
    saveJson (ctx.home / "deployment.json") (Deployment.mk ctx.project "legacy" #[] 1 7)
    request (.createDir (ctx.directory "old"))
    saveJson (ctx.directory "old" / "trace.json") (Json.mkObj [])
    discard <| docker #["volume", "create", retired]
    let rejected ← cliCommand ctx #["deploy"] false
    require (rejected.exitCode != 0 && ((rejected.stdout ++ rejected.stderr).splitOn "'clean', then 'deploy'").length > 1)
      "Legacy deployment did not report the reset commands"
    require ((← readJson (α := Json) (Project.assets ctx / "config.json")) == legacy)
      "Failed deploy overwrote the old configuration"
    discard <| cliCommand ctx #["clean"]
    require (!(← request (.exists ctx.home))) "Clean retained the old deployment directory"
    require ((← docker #["volume", "inspect", retired] false).exitCode != 0) "Clean retained retired worker storage"
    require (!(← Deployments.load).entries.any (·.project == ctx.project)) "Clean retained the catalog entry"
    -- Everything from here goes through the real CLI executable.
    discard <| cliCommand ctx #["deploy", "--workers", "1"]
    discard <| cliCommand ctx #["programs"]
    discard <| cliCommand ctx #["status"]
    let config : Json ← readJson (Project.assets ctx / "config.json")
    require (config == (← liftExcept (Project.runtimeConfig Project.defaultConfig 1)))
      "Fresh deployment did not use HTTP/SQLite configuration"
    discard <| cliCommand ctx #["run", "sum-squares", "--id", "command-check"]
    let deadline := (← request .now) + 90000
    repeat
      let output ← cliCommand ctx #["result", "command-check"]
      if output.stdout.trimAscii.toString == "55" then break
      require (output.stdout.trimAscii.toString == "pending") s!"Unexpected workflow result: {output.stdout}"
      require ((← request .now) < deadline) "CLI workflow did not complete"
      request (.sleep 1000)
    let listing ← cliCommand ctx #["ps"]
    require ((listing.stdout.splitOn "STARTED (UTC)").length > 1 &&
      (listing.stdout.splitOn "FINISHED (UTC)").length > 1 &&
      (listing.stdout.splitOn "ELAPSED").length > 1) "ps omitted time columns"
    discard <| cliCommand ctx #["inspect", "command-check"]
    let finalView ← cliCommand ctx #["watch", "command-check", "--once"]
    require ((finalView.stdout.splitOn "LAST VIEW").length > 1 &&
      (finalView.stdout.splitOn "BRANCHES").length > 1 &&
      (finalView.stdout.splitOn "HISTORY").length == 1 &&
      (finalView.stdout.splitOn "report worker").length == 1) "Watch still displayed an execution timeline"
    require ((finalView.stdout.splitOn "ELAPSED").length > 1) "Tree omitted elapsed times"
    let run ← ctx.loadRun "command-check"
    let some timing ← ctx.timing run | throw "Scheduler did not expose timing metadata"
    require (timing.span.any (fun span => span.startedMs > 0 && span.finishedMs.isSome))
      "Completed run did not save its start and finish"
    require (timing.branches.size == 6 && timing.groups.size == 1 &&
      timing.branches.all (·.2.finishedMs.isSome) && timing.groups.all (·.2.finishedMs.isSome))
      "Branch or parallel timing missing"
    require (← request (.exists (ctx.directory "command-check" / "watch.json"))) "Final view was not saved"
    require (!(← request (.exists (ctx.directory "command-check" / "trace.json")))) "Watch retained an execution history"
    discard <| cliCommand ctx #["down"]
    discard <| cliCommand ctx #["up"]
    let some restored ← ctx.timing run | throw "Restart lost timings"
    require (restored.span == timing.span && restored.branches == timing.branches && restored.groups == timing.groups)
      "Restart changed completed durations"
    let result ← cliCommand ctx #["result", "command-check"]
    require (result.stdout.trimAscii.toString == "55") "Restart lost the completed result"
    discard <| cliCommand ctx #["clean"]
    for args in #[
      #["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project],
      #["ps", "-aq", "--filter", "label=com.docker.compose.project=" ++ ctx.project],
      #["network", "ls", "-q", "--filter", "label=com.docker.compose.project=" ++ ctx.project],
      #["volume", "ls", "-q", "--filter", "label=com.docker.compose.project=" ++ ctx.project],
      #["image", "ls", "-q", ctx.project ++ "-app"]] do
      require ((← docker args).stdout.trimAscii.isEmpty) s!"Clean left resources: {reprStr args}"
    for volume in deploymentVolumes 1 do
      require ((← docker #["volume", "inspect", ctx.project ++ "_" ++ volume] false).exitCode != 0)
        s!"Clean left storage: {volume}"
    require (!(← request (.exists ctx.home))) "Clean retained new workflow history"
    require (!(← Deployments.load).entries.any (·.project == ctx.project)) "Clean retained the new catalog entry"
    discard <| cliCommand ctx #["clean"]
    require ((← request (.readFile (root / "LeanCloud.lean"))) == source &&
      (← request (.readFile (root / "deploy/config.json"))) == defaults) "Commands changed application source or defaults"
    printLine "CLI lifecycle passed: legacy rejection → clean → deploy → run/result → down/up → clean, using real Docker services."
  finally
    -- Independent cleanup still runs if a CLI assertion fails. Keep command logs.
    cleanup ctx
    discard <| docker #["volume", "rm", retired] false

def run : Cli Unit := do
  commandLifecycle
  demo
  scaling
  poolChaos
  generatedApp

end LeanCloudTests.ConsoleRuntime

def main (args : List String) : IO UInt32 := do
  let program := match args with
    | [] => LeanCloudTests.ConsoleRuntime.run
    | ["--pool-only"] => LeanCloudTests.ConsoleRuntime.demo
    | ["--scaling-only"] => LeanCloudTests.ConsoleRuntime.scaling
    | ["--chaos-only"] => LeanCloudTests.ConsoleRuntime.poolChaos
    | ["--prepare-chaos-image"] => LeanCloudTests.ConsoleRuntime.prepareChaosImage
    | ["--chaos-only", "--seed", seed] => do
      let some seed := seed.toNat? | throw "--seed requires a natural number"
      LeanCloudTests.ConsoleRuntime.poolChaos seed
    | ["--app-only"] => LeanCloudTests.ConsoleRuntime.generatedApp
    | ["--lifecycle-only"] => LeanCloudTests.ConsoleRuntime.commandLifecycle
    | _ => throw "Usage: cloud_console_tests [--pool-only|--scaling-only|--chaos-only [--seed N]|--prepare-chaos-image|--app-only|--lifecycle-only]"
  -- Keep test registrations out of the user's deployment catalog.
  let catalog := (← IO.Process.getCurrentDir) / ".lean-cloud" / s!"console-catalog-test-{← IO.Process.getPID}"
  let result ← LeanCloudCli.withHostIO fun handle =>
    LeanCloudCli.Cli.runWith (fun op => match op with
      | .getEnv "LEAN_CLOUD_HOME" => pure (.ok (some catalog.toString))
      | .getEnv "LEAN_CLOUD_PROJECT" => pure (.ok none)
      | other => handle other) program
  match result with
  | .ok () => return 0
  | .error error => IO.eprintln error; return 1
