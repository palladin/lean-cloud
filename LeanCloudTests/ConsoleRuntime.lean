import LeanCloudCli.Console
import LeanCloudCli.IO

namespace LeanCloudTests.ConsoleRuntime
open Lean LeanCloud LeanCloudCli

private def require (condition : Bool) (message : String) : Cli Unit :=
  unless condition do throw message

private partial def awaitOutcome (ctx : Context) (run : Run) (deadline : Nat) : Cli Exit := do
  -- Blob volumes may still be registering after the service health check passes.
  let result ← observing (ctx.outcome run)
  if let .ok (some outcome) := result then return outcome
  unless (← request .now) < deadline do
    match result with
    | .error error => throw s!"Console result unavailable: {error}"
    | _ => throw "Console run timed out"
  request (.sleep 250)
  awaitOutcome ctx run deadline

private def waitFor (ctx : Context) (run : Run) (expected : Nat) : Cli Unit := do
  match ← awaitOutcome ctx run ((← request .now) + 90000) with
  | .success json =>
    let actual ← liftExcept (Codec.decode (α := Nat) json)
    require (actual == expected) "Console run returned a different result"
  | _ => throw "Console run failed"

private def poolNodes (ctx : Context) : Cli String := do
  let count := (← ctx.deployment).workers
  let actors := (#["scheduler"] ++ workerNames count).map ctx.node
  let states ← docker (#["inspect", "--format", "{{.State.Running}} {{.HostConfig.RestartPolicy.Name}}"] ++ actors)
  require (states.stdout.trimAscii.toString.splitOn "\n" == List.replicate (count + 1) "true unless-stopped")
    "Persistent pool is not running"
  let nodes ← ctx.nodes
  require (nodes.size == count + 2 && nodes.all (fun node => (deploymentServices count).contains node.role))
    "Deployment must contain the configured combined nodes and blob storage"
  for actor in actors do
    discard <| docker #["exec", actor, "cloud-node", "health"]
  let ids ← docker (#["inspect", "--format", "{{.Id}}"] ++ actors)
  return ids.stdout

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

private def cleanup (ctx : Context) : Cli Unit := do
  let nodes ← docker #["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project] false
  let ids := nodes.stdout.splitOn "\n" |>.filter (!·.isEmpty) |>.toArray
  if !ids.isEmpty then discard <| docker (#["rm", "-f"] ++ ids) false
  discard <| ctx.compose #["down", "-v", "--remove-orphans"]
  let count ← try pure (← ctx.deployment).retainedCount catch _ => pure defaultWorkerCount
  for volume in deploymentVolumes count do
    discard <| docker #["volume", "rm", ctx.project ++ "_" ++ volume] false
  let images ← docker #["image", "ls", "--format", "{{.Repository}}:{{.Tag}}", ctx.project ++ "-app"] false
  for tag in images.stdout.splitOn "\n" do
    if tag.startsWith (ctx.project ++ "-app:") then discard <| docker #["image", "rm", tag] false

def demo : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let ctx : Context := ⟨root, s!"lean-cloud-console-test-{← request .pid}"⟩
  Deployments.isolate ctx
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
    let histories ← ctx.events second
    require (histories.any (fun (_, events) => !events.isEmpty)) "Workers emitted no execution observations"
    require (histories.all (fun (_, events) => events.all (·.run == second.id))) "Watch crossed run traces"
    let recorded ← LeanCloudCli.Trace.load ctx second
    require (recorded.steps.any fun step => step.resources.any fun sample =>
      sample.cpuNs.isSome && sample.memory.any (· > 0) && sample.memoryLimit.any (· > 0))
      "Worker resource metrics were not recorded with the trace"
    let nodes := runNodes first (← ctx.nodes)
    require (nodes.all (fun n => n.run.isNone || n.run == some "first")) "Watch included another run's actors"
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
    -- Pause preserves execution records and disables restart, while other runs
    -- still use the shared services. Kill is terminal and can be retried.
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
    require ((← ctx.outcome killed) == some (.cancelled "Killed by user")) "Kill did not publish cancellation"
    discard (command ctx ["watch", "killed", "--once"])
    let killedTrace ← LeanCloudCli.Trace.load ctx killed
    require (killedTrace.steps.any (·.event.activity == "sealed")) "Killed run lost its scheduler event"
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
    require (offlineTrace.steps.size ≥ killedTrace.steps.size && !offlineTrace.warning.isEmpty)
      "Shutdown discarded observed execution steps"
    require (offlineTrace.steps.any (·.resources.isSome)) "Shutdown lost historical worker metrics"
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
    for role in #["scheduler", "worker1", "worker2", "worker3"] do
      let output ← docker #["logs", "--tail", "100", ctx.node role] false
      request (.writeFile (ctx.home / s!"failure-{role}.log") (output.stdout ++ output.stderr))
    throw error
  finally
    cleanup ctx
    printLine s!"Console test catalog retained: {ctx.home}"

/-- Real scale changes during execution, using the same compiled application,
HTTP/SQLite nodes, scheduler state machine, and replay interpreter. -/
def scaling : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let ctx : Context := ⟨root, s!"lean-cloud-scaling-test-{← request .pid}"⟩
  Deployments.isolate ctx
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
    for role in #["scheduler"] ++ workerNames 4 do
      let logs ← docker #["logs", "--tail", "120", ctx.node role] false
      request (.writeFile (ctx.home / s!"failure-{role}.log") (logs.stdout ++ logs.stderr))
    throw error
  finally cleanup ctx

def generatedApp : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let owner : Context := ⟨root, s!"lean-cloud-app-test-{← request .pid}"⟩
  let directory := owner.home / "application-test"
  Project.init owner directory.toString (some root.toString)
  let ctx : Context := ⟨directory, owner.project⟩
  Deployments.isolate ctx
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

def run : Cli Unit := do
  demo
  scaling
  generatedApp

end LeanCloudTests.ConsoleRuntime

def main (args : List String) : IO UInt32 := do
  let program := match args with
    | [] => LeanCloudTests.ConsoleRuntime.run
    | ["--pool-only"] => LeanCloudTests.ConsoleRuntime.demo
    | ["--scaling-only"] => LeanCloudTests.ConsoleRuntime.scaling
    | ["--app-only"] => LeanCloudTests.ConsoleRuntime.generatedApp
    | _ => throw "Usage: cloud_console_tests [--pool-only|--scaling-only|--app-only]"
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
