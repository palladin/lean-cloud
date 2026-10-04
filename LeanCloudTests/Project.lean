import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open Lean LeanCloudCli

def projectCases : Array TestCase := #[
  ⟨"console.project.worker-count-templates", do
    for count in [0, 1, 5, 12] do
      let config ← unwrap (Project.runtimeConfig Project.defaultConfig count)
      let routes ← unwrap (config.getObjVal? "mailboxes" >>= (·.getObjValAs? (Array Json) "workers"))
      assertEq routes.size count
      for i in [:count] do
        assertEq (routes[i]!.getObjValAs? String "worker").toOption (some s!"worker{i + 1}")
        assertEq (routes[i]!.getObjVal? "broker" >>= (·.getObjValAs? String "host")).toOption
          (some s!"worker{i + 1}-mailbox")
      let resized ← unwrap (Project.runtimeConfig config (count + 2))
      assertEq ((← unwrap (resized.getObjVal? "blobs")).compress) ((← unwrap (config.getObjVal? "blobs")).compress)
      let volumes ← unwrap ((Project.compose ⟨"/work", "app"⟩ ⟨"app", "app", count⟩ "4.34.1" none).getObjVal? "volumes" >>= Json.getObj?)
      assertEq volumes.size (count + 3)⟩,
  ⟨"console.project.legacy-default-worker-count", do
    let app : Project.App ← unwrap (fromJson? (Json.mkObj [("name", toJson "app"), ("executable", toJson "app")]))
    assertEq app.workers 3
    let deployment : Deployment ← unwrap (fromJson? (Json.mkObj [("project", toJson "app"),
      ("image", toJson "image"), ("programs", toJson (#[] : Array LeanCloud.ProgramInfo))]))
    assertEq deployment.retainedCount 3⟩,
  ⟨"console.project.init-selects-app", do
    let (result, world) := ConsoleModel.run (dispatch ⟨"/work", "test"⟩ ["init", "my-app"]) {}
    let (ctx, running) ← unwrap result
    assertEq ctx.root.toString "/work/my-app"
    assertEq ctx.project "my-app"
    assertTrue running "Creating an app closed the console"
    assertTrue world.processes.isEmpty "Creating an app started containers"⟩,
  ⟨"console.project.open-selects-app", do
    let initial := ({ directories := #["/work", "/work/app"] } : ConsoleModel.World).json "/work/app/lean-cloud.json" (Project.App.mk "custom-name" "my_worker" defaultWorkerCount)
    let (result, _) := ConsoleModel.run (dispatch ⟨"/work", "test"⟩ ["open", "app"]) initial
    let (ctx, running) ← unwrap result
    assertEq ctx.root.toString "/work/app"
    assertEq ctx.project "custom-name"
    assertTrue running "Opening an app closed the console"⟩,
  ⟨"console.project.open-rejects-file", do
    let initial := ({} : ConsoleModel.World).save "/work/Main.lean" "user code"
    let (result, _) := ConsoleModel.run (dispatch ⟨"/work", "test"⟩ ["open", "Main.lean"]) initial
    assertTrue result.toOption.isNone "A source file was selected as an app directory"⟩,
  ⟨"console.project.local-sdk-is-portable", do
    let initial := ({} : ConsoleModel.World).save "/work/runtime/LeanCloudRuntime/Application.lean" ""
    let (result, world) := ConsoleModel.run (Project.init ⟨"/work", "test"⟩ "my-app") initial
    discard (unwrap result)
    assertTrue (world.file "/work/my-app/lean-cloud.local.json").isSome "Local SDK was not selected"
    let lakefile := (world.file "/work/my-app/lakefile.lean").getD ""
    assertTrue ((lakefile.splitOn "/work").length == 1) "Lake package contains a machine-specific path"⟩,
  ⟨"console.project.scaffold", do
    let ctx : Context := ⟨"/work", "test"⟩
    let (result, world) := ConsoleModel.run (Project.init ctx "my-app") {}
    discard (unwrap result)
    let source := (world.file "/work/my-app/Main.lean").getD ""
    assertTrue ((source.splitOn "Application.main").length > 1) "No reusable entry point"
    assertTrue ((source.splitOn "name := \"my-app\"").length > 1) "App name missing"
    assertTrue ((source.splitOn "program.register").length > 1) "Generated app does not register its source map"
    for file in ["Main.lean", "lean-toolchain", "lakefile.lean", "lean-cloud.json", ".gitignore"] do
      assertTrue (world.file (System.FilePath.mk "/work/my-app" / file)).isSome s!"Missing {file}"
    assertTrue (world.file "/work/my-app/Dockerfile").isNone "Scaffold exposed Docker boilerplate"
    assertTrue world.processes.isEmpty "Scaffolding executed processes"⟩,
  ⟨"console.project.preserve-existing-files", do
    let world : ConsoleModel.World := { directories := #["/work", "/work/my-app"] }
    let world := world.save "/work/my-app/Main.lean" "my code"
    let (result, after) := ConsoleModel.run (Project.init ⟨"/work", "test"⟩ "my-app") world
    assertTrue result.toOption.isNone "Existing project overwritten"
    assertEq after.files world.files⟩,
  ⟨"console.project.generated-services", do
    let ctx : Context := ⟨"/work/my-app", "my-app"⟩
    let initial := ({} : ConsoleModel.World).json (Project.manifest ctx.root) (Project.App.mk "my-app" "cloud_app" defaultWorkerCount)
      |>.save (ctx.root / "lean-toolchain") "leanprover/lean4:v4.34.1\n"
      |>.save (ctx.root / ".dockerignore") "private-data/\n"
    let (result, world) := ConsoleModel.run (Project.prepare ctx) initial
    discard (unwrap result)
    let compose ← unwrap (Json.parse (world.file (Project.assets ctx / "compose.json")).get!)
    let services ← unwrap (compose.getObjVal? "services")
    for name in ["worker", "blobs"] do
      assertTrue (services.getObjVal? name).toOption.isSome s!"Missing service {name}"
    assertTrue (services.getObjVal? "scheduler-mailbox").toOption.isNone "Generated a separate mailbox container"
    for role in ["scheduler", "worker1", "worker2", "worker3"] do
      assertTrue (compose.getObjVal? "volumes" >>= (·.getObjVal? (role ++ "-mailbox-data"))).toOption.isSome
        "Missing durable mailbox volume"
    assertTrue (world.file (Project.assets ctx / "node.c")).isSome "Missing native node entry point"
    let args ← unwrap ((services.getObjVal? "worker") >>= (·.getObjVal? "build") >>= (·.getObjVal? "args"))
    assertEq (args.getObjValAs? String "LEAN_VERSION").toOption (some "4.34.1")
    assertEq (args.getObjValAs? String "APP_TARGET").toOption (some "cloud_app")
    assertTrue (((world.file (Project.assets ctx / "Dockerfile.dockerignore")).getD "").startsWith "private-data/") "User ignores lost"
    assertTrue world.processes.isEmpty "Preparing assets started containers"⟩,
  ⟨"console.project.validate-target-before-build", do
    for target in ["../other", "app;touch", "app\nRUN bad", "", "app --help"] do
      let app : Project.App := ⟨"test", target, defaultWorkerCount⟩
      let initial := ({} : ConsoleModel.World).json "/work/lean-cloud.json" app
      let (result, world) := ConsoleModel.run (Project.load "/work") initial
      assertTrue result.toOption.isNone s!"Invalid target accepted: {target}"
      assertTrue world.processes.isEmpty "Invalid target executed a process"⟩,
  ⟨"console.project.name-selects-deployment", do
    let initial := ({} : ConsoleModel.World).json "/work/lean-cloud.json" (Project.App.mk "my-app" "cloud_app" defaultWorkerCount)
    let (result, world) := ConsoleModel.run (application []) { initial with keys := [4] }
    assertEq (← unwrap result) 0
    assertTrue ((world.stdout.splitOn "lean-cloud  /  my-app").length > 1) "Wrong project selected"⟩
]

end LeanCloudTests
