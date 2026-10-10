import LeanCloudCli.Model
import LeanCloud.ExecutionConfig

namespace LeanCloudCli.Project
open Lean

structure App where
  name : String
  executable : String := "cloud_app"
  workers : Nat := defaultWorkerCount
  worker : LeanCloud.ExecutionConfig := {}
  deriving ToJson

instance : FromJson App where
  fromJson? json := do
    return {
      name := ← json.getObjValAs? String "name"
      executable := ← jsonFieldD json "executable" "cloud_app"
      workers := ← jsonFieldD json "workers" defaultWorkerCount
      worker := ← jsonFieldD json "worker" {} }

def manifest (root : System.FilePath) := root / "lean-cloud.json"
def localConfig (root : System.FilePath) := root / "lean-cloud.local.json"
def assets (ctx : Context) := ctx.home / "deployment"

def load (root : System.FilePath) : Cli App := do
  let app ← readJson (α := App) (manifest root)
  validateId app.name
  unless app.name == app.name.toLower do throw "Application name must be lowercase"
  unless !app.executable.isEmpty && app.executable.toList.all (fun c =>
      c.toNat < 128 && (c.isAlphanum || c == '_')) do throw "Invalid Lake executable target"
  return app

def sdk (root : System.FilePath) : Cli (Option String) := do
  unless ← request (.exists (localConfig root)) do return none
  let config ← readJson (α := Json) (localConfig root)
  let path ← liftExcept (config.getObjValAs? String "sdk")
  return some (← request (.realPath path)).toString

def openDirectory (ctx : LeanCloudCli.Context) (directory : String) : Cli LeanCloudCli.Context := do
  let root ← request (.realPath (ctx.root / directory))
  unless ← request (.isDir root) do throw "Expected an application directory"
  let name ← if ← request (.exists (manifest root)) then pure (← load root).name else pure "lean-cloud-console"
  let project := (← request (.getEnv "LEAN_CLOUD_PROJECT")).getD name
  validateId project
  unless project == project.toLower do throw "Deployment project must be lowercase"
  return ⟨root, project⟩

/-- Create only application source and package metadata. Deployment files are generated later. -/
def init (ctx : Context) (directory : String) (localSdk : Option String := none) : Cli Unit := do
  let target := ctx.root / directory
  let name := target.fileName.getD ""
  validateId name
  unless name == name.toLower && name.toList.head!.isAlpha do
    throw "Use an application name beginning with a lowercase letter"
  if ← request (.exists target) then
    unless (← request (.readDir target)).isEmpty do throw "Destination is not empty; no files were changed"
  let localSdk ← match localSdk with
    | some path => pure (some (← request (.realPath (ctx.root / path))).toString)
    | none =>
      if ← request (.exists (ctx.root / "runtime/LeanCloudRuntime/Application.lean")) then
        pure (some ctx.root.toString)
      else pure none
  if let some path := localSdk then
    unless ← request (.exists (System.FilePath.mk path / "runtime/LeanCloudRuntime/Application.lean")) do
      throw "SDK checkout does not contain the reusable application runtime"
  request (.createDir target)
  let app : App := { name }
  request (.writeFile (target / "lean-toolchain") (include_str "../lean-toolchain"))
  request (.writeFile (target / "Main.lean") ((include_str "Templates/Main.lean.in").replace "APP_NAME" name))
  request (.writeFile (target / "lakefile.lean") ((include_str "Templates/lakefile.lean.in").replace "APP_NAME" name))
  request (.writeFile (manifest target) (toJson app).pretty)
  request (.writeFile (target / ".gitignore") ".lake/\n.lean-cloud/\nlean-cloud.local.json\n")
  if let some path := localSdk then
    request (.writeFile (localConfig target) (Json.mkObj [("sdk", toJson path)]).pretty)
  printLine s!"Created {target}. Edit Main.lean, then use 'deploy' from this application's console."

def defaultConfig : Json := Json.parse (include_str "../deploy/config.json") |>.toOption.getD Json.null

/-- Preserve existing routes and credentials; instantiate new mailbox routes
from the first worker's HTTP endpoint configuration. -/
def runtimeConfig (config : Json) (workers : Nat) : Except String Json := do
  LeanCloud.Version.check "formatVersion" "runtime configuration" config
  let limits : LeanCloud.ExecutionConfig ← jsonFieldD config "worker" {}
  limits.validate
  let mailboxes ← config.getObjVal? "mailboxes"
  let existing ← mailboxes.getObjValAs? (Array Json) "workers"
  if existing.any (fun route => (route.getObjVal? "broker").isOk) then
    throw "This deployment still has saved RabbitMQ configuration. Run 'clean', then 'deploy' to create an HTTP/SQLite deployment. 'clean' permanently deletes this deployment's workflows, results, and locally hosted blobs. Existing queues are not migrated."
  let prototype ← match existing[0]? with
    | some route => route.getObjVal? "endpoint"
    | none => mailboxes.getObjVal? "scheduler"
  let routes := (workerNames workers).map fun name =>
    (existing.find? (fun route => (route.getObjValAs? String "worker").toOption == some name)).getD
      (Json.mkObj [("worker", toJson name),
        ("endpoint", prototype.setObjVal! "host" (toJson (name ++ "-mailbox")))])
  return LeanCloud.Version.stamp "formatVersion"
    (config.setObjVal! "mailboxes" (mailboxes.setObjVal! "workers" (toJson routes)))

private def sdkCopy : String := "COPY --from=sdk lean-toolchain lakefile.lean lake-manifest.json /opt/lean-cloud/\n" ++
  "COPY --from=sdk runtime/lakefile.lean runtime/lake-manifest.json /opt/lean-cloud/runtime/\n" ++
  -- Compile in the application's workspace, so Lake uses the same transitive
  -- package directories here and when it links the final executable.
  "WORKDIR /src\nCOPY lakefile.lean lean-toolchain ./\n" ++
  "RUN lake -KleanCloudSdk=/opt/lean-cloud update lean_cloud_runtime && " ++
  "lake -KleanCloudSdk=/opt/lean-cloud build LeanEff LeanLinq LeanLinq.Driver.Sqlite\n" ++
  "COPY --from=sdk LeanCloud.lean /opt/lean-cloud/\n" ++
  "COPY --from=sdk LeanCloud /opt/lean-cloud/LeanCloud\n" ++
  "COPY --from=sdk LeanCloudCli /opt/lean-cloud/LeanCloudCli\n" ++
  "COPY --from=sdk native /opt/lean-cloud/native\n" ++
  "COPY --from=sdk deploy /opt/lean-cloud/deploy\n" ++
  "COPY --from=sdk runtime/LeanCloudRuntime.lean /opt/lean-cloud/runtime/\n" ++
  "COPY --from=sdk runtime/LeanCloudRuntime /opt/lean-cloud/runtime/LeanCloudRuntime\n" ++
  "COPY --from=sdk runtime/native /opt/lean-cloud/runtime/native\n" ++
  "RUN lake -KleanCloudSdk=/opt/lean-cloud build LeanCloudRuntime"

def dockerfile (localSdk : Bool) : String :=
  (include_str "Templates/Dockerfile")
    |>.replace "# SDK_CONTEXT" (if localSdk then sdkCopy else "")
    |>.replace "# BUILD_APP" ("RUN " ++ (if localSdk then
      "lake -KleanCloudSdk=/opt/lean-cloud update lean_cloud_runtime && " else "") ++
      "lake " ++ (if localSdk then "-KleanCloudSdk=/opt/lean-cloud " else "") ++
      "build \"$APP_TARGET\" && mkdir -p /out && cp \".lake/build/bin/$APP_TARGET\" /out/app")

private def volume (source target : String) : Json :=
  Json.mkObj [("type", toJson "bind"), ("source", toJson source), ("target", toJson target), ("read_only", toJson true)]

def compose (ctx : Context) (app : App) (version : String) (localSdk : Option String) : Json := Id.run do
  let home := assets ctx
  let mut services := []
  let mut volumes := [("scheduler-data", Json.mkObj []), ("blob-data", Json.mkObj [])]
  for name in #["scheduler"] ++ workerNames app.workers do
    volumes := volumes ++ [(name ++ "-mailbox-data", Json.mkObj [])]
  services := services ++ [("blobs", Json.mkObj [
    ("image", toJson "chrislusf/seaweedfs:4.48"), ("restart", toJson "unless-stopped"),
    ("command", toJson #["server", "-ip=blobs", "-ip.bind=0.0.0.0", "-dir=/data", "-volume.max=20", "-master.volumeSizeLimitMB=100", "-filer", "-s3", "-s3.config=/etc/seaweedfs/s3.json"]),
    ("volumes", toJson #[toJson "blob-data:/data", volume (home / "s3.json").toString "/etc/seaweedfs/s3.json",
      volume (home / "filer.toml").toString "/etc/seaweedfs/filer.toml"]),
    ("healthcheck", Json.mkObj [("test", toJson #["CMD-SHELL", "wget -S -O /dev/null http://localhost:8333/ 2>&1 | grep -q 'HTTP/1.1 403'"]),
      ("interval", toJson "2s"), ("timeout", toJson "3s"), ("retries", toJson (30 : Nat))])])]
  let build := Json.mkObj ([("context", toJson ctx.root.toString), ("dockerfile", toJson (home / "Dockerfile").toString),
    ("args", Json.mkObj [("APP_TARGET", toJson app.executable), ("LEAN_VERSION", toJson version)])] ++
    [("additional_contexts", Json.mkObj ([("node_assets", toJson home.toString)] ++
      localSdk.toList.map (fun path => ("sdk", toJson path))))])
  services := services ++ [("worker", Json.mkObj [("build", build), ("image", toJson (ctx.project ++ "-app:build"))])]
  return Json.mkObj [("services", Json.mkObj services), ("volumes", Json.mkObj volumes)]

/-- All generated infrastructure lives in the ignored deployment directory. -/
def prepare (ctx : Context) (workers : Option Nat := none) (writeConfig := true) : Cli Unit := do
  let app ← load ctx.root
  let app := { app with workers := workers.getD app.workers }
  let toolchain := (← request (.readFile (ctx.root / "lean-toolchain"))).trimAscii.toString
  unless toolchain.startsWith "leanprover/lean4:v" do throw "Deployment needs a versioned Lean release in lean-toolchain"
  let version := toolchain.drop "leanprover/lean4:v".length |>.toString
  unless !version.isEmpty && version.toList.all (fun c => c.isDigit || c == '.') do throw "Invalid Lean release version"
  let localSdk ← sdk ctx.root
  let home := assets ctx
  let ignore ← if ← request (.exists (ctx.root / ".dockerignore")) then
    request (.readFile (ctx.root / ".dockerignore")) else pure ""
  request (.createDir home)
  for (name, text) in [("Dockerfile", dockerfile localSdk.isSome),
      ("Dockerfile.dockerignore", ignore ++ "\n.git\n**/.lake\n**/.lean-cloud\nlean-cloud.local.json\n**/.DS_Store\n"),
      ("node.c", include_str "Templates/node.c"), ("s3.json", include_str "../deploy/s3.json"),
      ("filer.toml", include_str "../deploy/filer.toml"),
      ("compose.json", (compose ctx app version localSdk).pretty)] do
    request (.writeFile (home / name) text)
  if writeConfig then
    saveJson (home / "config.json") (← liftExcept (runtimeConfig
      (defaultConfig.setObjVal! "worker" (toJson app.worker)) app.workers))

end LeanCloudCli.Project
