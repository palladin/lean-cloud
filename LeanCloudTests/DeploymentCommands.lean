import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open Lean LeanCloudCli
open ConsoleModel (World Invocation)

private def ctx : Context := ⟨"/work", "demo"⟩
private def registry : System.FilePath := "/home/test/.local/state/lean-cloud/deployments.json"
private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1
private def output (text := "") : Except String ProcessOutput := .ok { stdout := text }

private def healthyNodes : Json := toJson (deploymentServices.map fun service => Json.mkObj [
  ("Name", toJson ("/demo-" ++ service)),
  ("State", Json.mkObj [("Status", toJson "running"), ("StartedAt", toJson "boot"),
    ("Health", Json.mkObj [("Status", toJson "healthy")])]),
  ("Config", Json.mkObj [("Labels", Json.mkObj [("com.docker.compose.service", toJson service)])])])

private def process (call : Invocation) : Except String ProcessOutput := do
  unless call.command == "docker" do throw "Unexpected executable"
  match call.args.toList with
  | ["--version"] | ["compose", "version"] | ["info", "--format", _] => output "version"
  | "ps" :: _ => output (if call.args.any (·.startsWith "label=com.docker.compose.service=") then "" else "node\n")
  | "inspect" :: _ => output (if call.args.contains "--format" then "healthy\nhealthy\nhealthy\nhealthy\n" else healthyNodes.compress)
  | "image" :: "inspect" :: _ => output (if call.args.contains "{{index .Config.Labels \"lean-cloud.node\"}}" then "mailbox-v1" else "sha256:pinned")
  | ["volume", "inspect", _] => output
  | "exec" :: _ => output
  | "compose" :: _ => output
  | ["container", "inspect", _] => return { exitCode := 1 }
  | "run" :: "-d" :: _ => output
  | _ => throw s!"Unexpected Docker request: {reprStr call.args}"

private def base : World :=
  ({ process, directories := #["/work", "/work/.lean-cloud", ctx.home.toString] } : World)
    |>.save "/work/compose.yaml" "services: {}"
    |>.json "/work/deploy/config.json" Project.defaultConfig
    |>.json (ctx.home / "deployment.json") (Deployment.mk ctx.project "sha256:pinned" #[] defaultWorkerCount 0)

private def checked (program : Cli α) (world : World := base) : IO (α × World) := do
  let (result, world) := ConsoleModel.run program world
  return (← unwrap result, world)

def deploymentCommandCases : Array TestCase := #[
  ⟨"console.deployment.up-output-flags", do
    let noise := "Service startup output\n"
    for args in [["up"], ["up", "-v"], ["up", "--verbose"]] do
      let (_, world) ← checked (command ctx args) { base with stream := some (fun _ =>
        .ok [{ stderr := noise.toUTF8, exitCode := some 0 }]) }
      assertEq world.stderr (if args.length > 1 then noise else "")
      let logs := world.files.filter (fun (path, _) => path.endsWith ".log")
      assertEq (logs.map Prod.snd) #[noise]
      assertTrue (has world.stdout "Starting blob" && has world.stdout "— done") "No startup progress"
      assertTrue world.locks.isEmpty "Startup leaked lock"⟩,
  ⟨"console.deployment.catalog-ownership-survives-discovery", do
    let test : Context := ⟨"/work", "another"⟩
    let catalog : Deployments.Catalog := {
      entries := #[⟨ctx.project, "/work"⟩, ⟨test.project, "/work"⟩]
      selected := some test.project }
    let initial := base.json registry catalog
      |>.json (test.home / "deployment.json") (Deployment.mk test.project "test-image" #[] defaultWorkerCount 0)
      |>.json (test.home / "catalog-owner.json") ("/isolated" : String)
    let (visible, world) ← checked (do Deployments.discover ctx; Deployments.load) initial
    assertEq (visible.entries.map (·.project)) #[ctx.project]
    assertEq visible.selected none "Selected a deployment owned by another catalog"
    let (_, listed) ← checked (listDeployments ctx) world
    assertTrue (!has listed.stdout test.project) "Retained test artifacts leaked into deployments"
    let isolated := { initial with envs := #[("LEAN_CLOUD_HOME", "/isolated")] }
    let (visible, _) ← checked (do Deployments.remember test; Deployments.load) isolated
    assertEq (visible.entries.map (·.project)) #[test.project] "Isolation hid the test from its own catalog"
    assertEq (world.file (test.home / "deployment.json")) (initial.file (test.home / "deployment.json"))
      "Discovery altered retained test artifacts"⟩,
  ⟨"console.deployment.selection-persists", do
    let other : Context := ⟨"/other", "second"⟩
    let initial := { base with directories := base.directories.push "/other" }
    let ((selected, _), world) ← checked (do
      Deployments.remember ctx
      Deployments.remember other
      dispatch other ["use", "demo"]) initial
    assertEq selected.root.toString "/work"
    assertEq selected.project "demo"
    let (restored, _) ← checked (Deployments.initial other) world
    assertEq restored.project "demo"
    let (overridden, _) ← checked (Deployments.initial other) { world with env := some "second" }
    assertEq overridden.project "second"
    let broken := world.save (other.home / "deployment.json") "broken JSON"
    let ((selected, _), _) ← checked (dispatch other ["use", "demo"]) broken
    assertEq selected.project "demo" "An unrelated broken deployment blocked switching"
    assertTrue world.processes.isEmpty "Selecting a deployment ran Docker"
    assertTrue world.locks.isEmpty "Selection leaked a lock"⟩,
  ⟨"console.deployment.name-collision", do
    let (_, world) ← checked (Deployments.remember ctx)
    let (result, after) := ConsoleModel.run (Context.deploy ⟨"/another", "demo"⟩) world
    assertTrue result.toOption.isNone "A second directory took ownership of the same Docker project"
    assertEq after.files world.files
    assertTrue (after.processes.isEmpty && after.locks.isEmpty) "Conflict mutated Docker or leaked lock"⟩,
  ⟨"console.deployment.import-down-and-offline", do
    let handler (call : Invocation) :=
      if call.args[0]? == some "ps" then output else process call
    let (_, down) ← checked (listDeployments ctx) { base with process := handler }
    assertTrue (has down.stdout "demo" && has down.stdout "down") "Stopped deployment was lost"
    assertTrue (down.file registry).isSome "Legacy deployment was not indexed"
    let (_, offline) ← checked (listDeployments ctx) { down with stdout := "", process := fun _ => .error "daemon unavailable" }
    assertTrue (has offline.stdout "Docker unavailable" && !has offline.stdout "down") "Offline daemon was reported as stopped"⟩,
  ⟨"console.deployment.corrupt-catalog-preserved", do
    let initial := base.save registry "broken JSON"
    let (result, after) := ConsoleModel.run (Deployments.remember ctx) initial
    assertTrue result.toOption.isNone "Corrupt catalog was silently replaced"
    assertEq after.files initial.files
    assertTrue after.locks.isEmpty "Catalog error leaked lock"
    let (code, help) ← checked (application ["--help"]) initial
    assertEq code 0 "Corrupt selection blocked help"
    assertTrue (help.stderr.isEmpty && !help.trace.contains "readFile") "Help consulted broken deployment state"
    assertEq help.files initial.files
    let (code, diagnosis) ← checked (application ["doctor"]) initial
    assertEq code 1
    assertTrue (has diagnosis.stdout "[fail] Deployment catalog") "Corrupt catalog blocked doctor"⟩,
  ⟨"console.deployment.missing-selection", do
    let (_, world) ← checked (Deployments.remember ⟨"/gone", "missing"⟩)
    let (result, _) := ConsoleModel.run (Deployments.select "missing") world
    assertTrue result.toOption.isNone "Selected a missing directory"
    let (fallback, after) ← checked (Deployments.initial ctx) world
    assertEq fallback.project ctx.project
    assertTrue (has after.stderr "directory is missing") "Missing selection silently ignored"⟩,
  ⟨"console.deployment.catalog-location", do
    let (home, _) ← checked Deployments.home { base with envs := #[("XDG_STATE_HOME", "/state")] }
    assertEq home.toString "/state/lean-cloud"
    let (home, _) ← checked Deployments.home { base with envs := #[("LEAN_CLOUD_HOME", "/portable"), ("XDG_STATE_HOME", "/state")] }
    assertEq home.toString "/portable"
    let (result, _) := ConsoleModel.run Deployments.home { base with envs := #[("LEAN_CLOUD_HOME", "relative")] }
    assertTrue result.toOption.isNone "Accepted relative catalog directory"⟩,
  ⟨"console.deployment.up-preserves-image-and-data", do
    let (_, after) ← checked (command ctx ["up"])
    assertEq (after.file (ctx.home / "deployment.json")) (base.file (ctx.home / "deployment.json"))
    assertTrue (after.processes.all (fun call => !call.args.contains "build" && !call.args.contains "create"))
      "up rebuilt the app or created scheduler storage"
    assertTrue (after.processes.any (fun call => call.args.contains "sha256:pinned")) "up lost pinned image"
    assertEq ((after.processes.filter (·.args.contains "up")).map (·.args.toList.drop 5))
      #[["--ansi", "never", "up", "-d", "--wait", "--no-build", "blobs"]]
    assertTrue after.locks.isEmpty "up leaked lock"⟩,
  ⟨"console.deployment.up-refuses-missing-storage", do
    let handler (call : Invocation) :=
      if call.args.toList == ["volume", "inspect", "demo_blob-data"] then
        .ok { exitCode := 1 : ProcessOutput } else process call
    let (result, after) := ConsoleModel.run ctx.up { base with process := handler }
    assertTrue result.toOption.isNone "up silently replaced missing durable storage"
    assertTrue (!after.processes.any (·.args.contains "up")) "Services started despite lost data"
    assertTrue after.locks.isEmpty "up failure leaked lock"⟩,
  ⟨"console.deployment.up-requires-combined-image", do
    let handler (call : Invocation) :=
      if call.args.contains "{{index .Config.Labels \"lean-cloud.node\"}}" then output "<no value>"
      else process call
    let (result, after) := ConsoleModel.run ctx.up { base with process := handler }
    let .error message := result | throw (IO.userError "Old image started as a combined node")
    assertTrue (has message "Use 'deploy'") "Missing image migration guidance"
    assertTrue (!after.processes.any (fun call => [some "run", some "stop", some "rm"].contains call.args[0]?))
      "Old image check modified actors or mailbox volumes"⟩,
  ⟨"console.deployment.status-health", do
    let (_, after) ← checked (command ctx ["status"])
    assertTrue (has after.stdout "Services:   up" && has after.stdout "Actors:     4 running") "Incorrect deployment summary"
    assertEq after.files base.files
    let partialNodes : Array Node := #[{ name := "broker", role := "worker1-mailbox", state := "running", started := "", health := some "unhealthy" }]
    assertEq (deploymentState partialNodes) "partial / check status"
    assertEq (serviceState partialNodes "worker1-mailbox") "unhealthy"
    assertEq (serviceState partialNodes "blobs") "absent"⟩,
  ⟨"console.deployment.doctor-read-only", do
    let (_, after) ← checked (command ctx ["doctor"])
    assertTrue (has after.stdout "All checks passed" && has after.stdout "not probed") "Diagnostic scope is unclear"
    assertEq after.files base.files
    assertEq after.directories base.directories
    assertTrue (after.processes.all (fun call => !call.args.contains "up" && !call.args.contains "run" && !call.args.contains "create"))
      "Doctor modified services"⟩,
  ⟨"console.deployment.doctor-offline", do
    let handler (call : Invocation) :=
      if call.args[0]? == some "info" then .ok { exitCode := 1 : ProcessOutput } else process call
    let initial := { base with process := handler, env := some "demo" }
    let (code, after) ← checked (application ["doctor"]) initial
    assertEq code 1
    assertTrue (has after.stdout "Start Docker" && has after.stderr "failed check") "Missing actionable daemon diagnosis"
    assertTrue (!after.processes.any (·.args[0]? == some "volume")) "Doctor ran dependent checks after daemon failure"⟩,
  ⟨"console.deployment.doctor-reports-multiple-failures", do
    let handler (call : Invocation) :=
      if call.args[0]? == some "volume" || call.args[0]? == some "image" then
        .ok { exitCode := 1 : ProcessOutput } else process call
    let (result, after) := ConsoleModel.run ctx.doctor { base with process := handler }
    assertTrue result.toOption.isNone "Missing deployment resources passed diagnosis"
    assertTrue (has after.stdout "Saved image is unavailable" && has after.stdout "Cannot access durable volume")
      "Doctor stopped at its first failure"⟩,
  ⟨"console.deployment.completion", do
    let (_, world) ← checked (Deployments.remember ctx)
    let (catalog, after) ← checked (Completion.load ctx) world
    assertEq ((Completion.candidates catalog (Completion.context "use d" 5)).map (·.value)) #["demo"]
    assertTrue after.processes.isEmpty "Completion contacted Docker"⟩
]

end LeanCloudTests
