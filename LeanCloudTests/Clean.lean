import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests.Clean
open Lean LeanCloudCli ConsoleModel

private def ctx : Context := ⟨"/work", "demo"⟩
private def catalogPath : System.FilePath := "/home/test/.local/state/lean-cloud/deployments.json"
private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1
private def output (text := "") : Except String ProcessOutput := .ok { stdout := text }

private def process (call : Invocation) : Except String ProcessOutput := do
  unless call.command == "docker" do throw "Unexpected host executable"
  match call.args.toList with
  | ["ps", "-aq", "--filter", "label=lean-cloud.project=demo"] => output "actor\nretired\n"
  | ["ps", "-aq", "--filter", "label=com.docker.compose.project=demo"] => output "blob\nretired\n"
  | ["network", "ls", "-q", "--filter", "label=com.docker.compose.project=demo"] => output "network\n"
  | ["volume", "ls", "-q", "--filter", "label=com.docker.compose.project=demo"] =>
      output "demo_blob-data\ndemo_legacy-broker\n"
  | ["volume", "ls", "-q"] => output "demo_scheduler-data\ndemo_scheduler-mailbox-data\ndemo_worker12-mailbox-data\ndemo_blob-data\ndemo_worker0-mailbox-data\ndemo_worker01-mailbox-data\ndemo_notes\ndemo-other_blob-data\nother_blob-data\n"
  | ["image", "ls", "--format", "{{.Repository}}:{{.Tag}}", "demo-app"] =>
      output "demo-app:build\ndemo-app:pinned\ndemo-app:pinned\ndemo-app:<none>\nother-app:keep\n"
  | ["stop", _] | ["rm", _] | ["network", "rm", _] | ["volume", "rm", _] | ["image", "rm", _] => output
  | _ => throw s!"Unexpected cleanup command: {reprStr call.args}"

private def initial : World :=
  ({ process, directories := #["/work", ctx.home.toString, (ctx.home / "runs").toString] } : World)
    |>.save "/work/Main.lean" "my program"
    |>.save "/work/lean-cloud.json" "application configuration"
    |>.save (ctx.home / "deployment.json") "deliberately unreadable old metadata"
    |>.save (ctx.home / "runs/run/trace.json") "history"
    |>.save "/work/.lean-cloud/demo-other/deployment.json" "another deployment"
    |>.json catalogPath ({ entries := #[⟨"demo", "/work"⟩, ⟨"other", "/elsewhere"⟩], selected := some "demo" } : Deployments.Catalog)

private def checked (program : Cli α) (world := initial) : IO (α × World) := do
  let (result, world) := ConsoleModel.run program world
  return (← unwrap result, world)

private def mutations (world : World) : Array (Array String) :=
  (world.processes.filter fun call => call.args.contains "rm" || call.args[0]? == some "stop").map (·.args)

def cases : Array TestCase := #[
  ⟨"console.clean.complete-and-isolated", do
    let (_, world) ← checked (command ctx ["clean"])
    assertEq (mutations world) #[#["stop", "actor"], #["stop", "retired"], #["stop", "blob"],
      #["rm", "actor"], #["rm", "retired"], #["rm", "blob"], #["network", "rm", "network"],
      #["volume", "rm", "demo_blob-data"], #["volume", "rm", "demo_legacy-broker"],
      #["volume", "rm", "demo_scheduler-data"], #["volume", "rm", "demo_scheduler-mailbox-data"],
      #["volume", "rm", "demo_worker12-mailbox-data"], #["image", "rm", "demo-app:build"], #["image", "rm", "demo-app:pinned"]]
    assertTrue (world.files.all (fun (path, _) => !path.startsWith (ctx.home.toString ++ "/"))) "Deployment files remain"
    assertTrue (!world.directories.contains ctx.home.toString) "Deployment directory remains"
    for path in ["/work/Main.lean", "/work/lean-cloud.json", "/work/.lean-cloud/demo-other/deployment.json"] do
      assertEq (world.file path) (initial.file path) "Cleanup touched application source or another deployment"
    let (catalog, _) ← checked Deployments.load world
    assertEq catalog.entries #[⟨"other", "/elsewhere"⟩]
    assertTrue catalog.selected.isNone "Removed deployment remained selected"
    assertTrue world.locks.isEmpty "Cleanup leaked a lock"
    assertTrue (has world.stdout "Removing deployment demo" && has world.stdout "Removed deployment demo") "Cleanup target was not visible"⟩,
  ⟨"console.clean.repeat-and-partial-deployments", do
    let (_, cleaned) ← checked ctx.clean
    let empty : Invocation → Except String ProcessOutput := fun call =>
      if call.args.contains "ls" || call.args[0]? == some "ps" then output else .error "No resources should remain"
    let (_, repeated) ← checked ctx.clean { cleaned with processes := #[], process := empty }
    assertTrue (mutations repeated).isEmpty "Repeating clean tried to remove absent resources"
    let failedBuild := { initial with files := initial.files.filter (fun (path, _) =>
      path != (ctx.home / "deployment.json").toString) }
    let (_, world) ← checked ctx.clean failedBuild
    assertTrue (world.files.all (fun (path, _) => !path.startsWith (ctx.home.toString ++ "/")))
      "Partial deployment without a manifest could not be removed"⟩,
  ⟨"console.clean.docker-failures-preserve-retry-state", do
    let (_, success) ← checked ctx.clean
    for args in mutations success do
      let handler (call : Invocation) := if call.args == args then
          Except.ok ({ exitCode := 1, stderr := "busy resource" } : ProcessOutput)
        else process call
      let (result, failed) := ConsoleModel.run ctx.clean { initial with process := handler }
      assertTrue result.toOption.isNone "Docker removal failure was ignored"
      assertEq failed.files initial.files "Recovery metadata was deleted before Docker cleanup succeeded"
      assertTrue (failed.locks.isEmpty && !failed.trace.contains "removeTree") "Failure leaked a lock or removed local state"
      assertTrue (match result with
        | .error message => has message "Cleanup incomplete"
        | .ok _ => false) "Cleanup failure had no retry guidance"
    let (result, offline) := ConsoleModel.run ctx.clean { initial with process := fun _ => .error "offline" }
    assertTrue result.toOption.isNone "Offline Docker was reported as cleaned"
    assertEq offline.files initial.files⟩,
  ⟨"console.clean.ownership-and-active-lock", do
    let another := initial.json catalogPath ({ entries := #[⟨"demo", "/another"⟩] } : Deployments.Catalog)
    let (result, world) := ConsoleModel.run ctx.clean another
    assertTrue result.toOption.isNone "Cleanup took another directory's deployment name"
    assertTrue world.processes.isEmpty "Ownership was checked after Docker changes"
    assertEq world.files another.files
    let (blocked, world) ← checked (ctx.withDeploymentLock (observing ctx.clean))
    assertTrue blocked.toOption.isNone "Concurrent deployment operation did not block cleanup"
    assertTrue (world.processes.isEmpty && world.locks.isEmpty) "Blocked cleanup touched Docker or leaked the outer lock"⟩,
  ⟨"console.clean.local-failures-can-be-retried", do
    let (_, success) ← checked ctx.clean
    let some deletion := success.trace.findIdx? (· == "removeTree") | throw (IO.userError "No filesystem cleanup")
    let (result, failed) := ConsoleModel.run ctx.clean { initial with failAt := some deletion }
    assertTrue result.toOption.isNone "Local deletion error was ignored"
    assertEq (failed.file catalogPath) (initial.file catalogPath) "Catalog was forgotten before local cleanup succeeded"
    assertTrue failed.locks.isEmpty "Local cleanup failure leaked a lock"
    let (_, recovered) ← checked ctx.clean { failed with failAt := none }
    assertTrue (recovered.file (ctx.home / "deployment.json")).isNone "Retry did not finish cleanup"⟩,
  ⟨"console.clean.help-and-completion", do
    let (_, world) ← checked (command ctx ["clean", "--help"])
    assertTrue (world.processes.isEmpty && has world.stdout "Permanently remove") "Cleanup help performed deletions"
    assertEq ((Completion.candidates {} (Completion.context "cle" 3)).map (·.value)) #["clean"]
    let (result, world) := ConsoleModel.run (command ctx ["clean", "unexpected"]) initial
    assertTrue (result.toOption.isNone && world.processes.isEmpty) "Invalid cleanup arguments changed deployment"⟩ ]

end LeanCloudTests.Clean
