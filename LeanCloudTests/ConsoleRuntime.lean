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

private def cleanup (ctx : Context) : Cli Unit := do
  let nodes ← docker #["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project] false
  let ids := nodes.stdout.splitOn "\n" |>.filter (!·.isEmpty) |>.toArray
  if !ids.isEmpty then discard <| docker (#["rm", "-f"] ++ ids) false
  discard <| ctx.compose #["down", "-v", "--remove-orphans"]
  discard <| docker #["volume", "rm", ctx.project ++ "_scheduler-data"] false
  let images ← docker #["image", "ls", "--format", "{{.Repository}}:{{.Tag}}", ctx.project ++ "-app"] false
  for tag in images.stdout.splitOn "\n" do
    if tag.startsWith (ctx.project ++ "-app:") then discard <| docker #["image", "rm", tag] false

private def demo : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let ctx : Context := ⟨root, s!"lean-cloud-console-test-{← request .pid}"⟩
  printLine s!"Console test project: {ctx.project}"
  try
    ctx.deploy
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
    discard <| docker #["tag", "rabbitmq:4.3", ctx.project ++ "-app:build"]
    ctx.resume "first"
    waitFor ctx first 29
    discard <| docker #["tag", deployment.image, ctx.project ++ "-app:build"]
    let histories ← ctx.events first
    require (histories.any (fun (_, events) => !events.isEmpty)) "Workers emitted no execution observations"
    let nodes := runNodes first (← ctx.nodes)
    require (nodes.all (fun n => n.run.isNone || n.run == some "first")) "Watch included another run's actors"
    require (nodes.toList.Pairwise (fun a b => a.name != b.name)) "Node inventory contains duplicate containers"
    let some source := first.program.source | throw "Missing bundled source"
    require (!source.sites.isEmpty) "No source locations bundled"
    discard (command ctx ["inspect", "first"])
    discard (command ctx ["watch", "first", "--once"])
    -- Completion and result inspection do not depend on a live scheduler.
    discard <| docker #["stop", ctx.container first "scheduler"]
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
    discard <| docker #["kill", ctx.container recover "worker1", ctx.container recover "scheduler"]
    ctx.resume "recover"
    discard <| awaitOutcome ctx recover ((← request .now) + 120000)
    require ((← ctx.remote recover "result") == "files=16, errors=24") "Recovery returned a different report"
    ctx.launch "log-summary" (some inputFile.toString) (some "shutdown")
    let interrupted ← ctx.loadRun "shutdown"
    require (← ctx.outcome interrupted).isNone "Shutdown test missed the active run"
    discard (command ctx ["down"])
    let actors ← docker #["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project]
    let services ← docker #["ps", "-aq", "--filter", "label=com.docker.compose.project=" ++ ctx.project]
    require (actors.stdout.trimAscii.isEmpty && services.stdout.trimAscii.isEmpty) "Shutdown left containers behind"
    ctx.down
    ctx.up
    waitFor ctx first 29
    ctx.resume "shutdown"
    discard <| awaitOutcome ctx interrupted ((← request .now) + 120000)
    require ((← ctx.remote interrupted "result") == "files=16, errors=24") "Run failed to resume after shutdown"
    printLine "Console tests passed: registry, validation, concurrent runs, image retention, typed results, source events, and completed recovery."
  finally
    cleanup ctx
    printLine s!"Console test catalog retained: {ctx.home}"

def generatedApp : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let owner : Context := ⟨root, s!"lean-cloud-app-test-{← request .pid}"⟩
  let directory := owner.home / "application-test"
  Project.init owner directory.toString (some root.toString)
  let ctx : Context := ⟨directory, owner.project⟩
  try
    -- Exercise an ordinary executable target, not the SDK's demonstration binary.
    let lakefile ← request (.readFile (directory / "lakefile.lean"))
    request (.writeFile (directory / "lakefile.lean") (lakefile.replace "lean_exe cloud_app" "lean_exe user_app"))
    -- Local editing creates a manifest containing host SDK paths. Deployment
    -- must re-resolve that dependency inside Docker without editing the host file.
    let checked ← request (.process "lake" #["-d", directory.toString, "build", "Main"] none)
    require (checked.exitCode == 0) (checked.stdout ++ checked.stderr)
    let manifest ← request (.readFile (directory / "lake-manifest.json"))
    ctx.deploy (some "user_app")
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
    saveJson (directory / "input.json") (toJson (#[2, 3, 4] : Array Nat))
    ctx.launch "application-test" (some "input.json") (some "custom")
    let custom ← ctx.loadRun "custom"
    waitFor ctx custom 29
    require ((← ctx.remote custom "result") == "29") "Reusable entry point lost the typed result"
    ctx.launch "application-test" none (some "sample")
    waitFor ctx (← ctx.loadRun "sample") 55
    ctx.down
    discard (command ctx ["deployments"])
    discard (command ctx ["status"])
    ctx.up
    require ((← ctx.deployment).image == deployment.image) "up replaced the pinned application image"
    discard (command ctx ["doctor"])
    waitFor ctx custom 29
    printLine "Standalone app tests passed: generated source, deployment catalog, selection, status, doctor, up without rebuilding, relative input, and typed results."
  finally
    cleanup ctx
    printLine s!"Standalone app retained: {directory}"

def run : Cli Unit := do
  demo
  generatedApp

end LeanCloudTests.ConsoleRuntime

def main (args : List String) : IO UInt32 := do
  let program := match args with
    | [] => LeanCloudTests.ConsoleRuntime.run
    | ["--app-only"] => LeanCloudTests.ConsoleRuntime.generatedApp
    | _ => throw "Usage: cloud_console_tests [--app-only]"
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
