import LeanCloudCli.Project
import LeanCloudCli.Deployments
import LeanCloudCli.Process

namespace LeanCloudCli
open Lean LeanCloud

/-- Arguments are always passed directly, never interpolated into a shell. -/
def docker (args : Array String) (check := true) (input : Option String := none) : Cli ProcessOutput := do
  let output ← request (.process "docker" args input)
  if check && output.exitCode != 0 then
    throw (safe (output.stdout ++ output.stderr).trimAscii.toString)
  return output

private def Context.dockerLogged (ctx : Context) (stage title : String)
    (args : Array String) (verbose : Bool) : Cli Unit := do
  let directory := ctx.home / "logs"
  request (.createDir directory)
  let stamp := s!"{stage}-{← request .pid}-{← request .now}"
  let mut suffix := 0
  let mut log := directory / s!"{stamp}.log"
  -- Called under the deployment lock; never overwrite a previous attempt's log.
  while ← request (.exists log) do
    suffix := suffix + 1
    log := directory / s!"{stamp}-{suffix}.log"
  printStyled (Styled.text ("… " ++ title) .yellow)
  request .flush
  Process.runLogged "docker" args log verbose
  printStyled (Styled.text ("✓ " ++ title ++ " — done") .green)
  request .flush

def Context.composeFile (ctx : Context) : Cli System.FilePath := do
  if ← request (.exists (Project.manifest ctx.root)) then
    pure (Project.assets ctx / "compose.json")
  else pure (ctx.root / "compose.yaml")

def Context.compose (ctx : Context) (args : Array String) : Cli ProcessOutput := do
  docker (#["compose", "-p", ctx.project, "-f", (← ctx.composeFile).toString] ++ args)

def Context.deployment (ctx : Context) : Cli Deployment := do
  let path := ctx.home / "deployment.json"
  unless ← request (.exists path) do throw "Run 'deploy' first"
  let deployment ← readJson (α := Deployment) path
  unless deployment.project == ctx.project do throw "Deployment context mismatch"
  return deployment

def Context.loadRun (ctx : Context) (id : String) : Cli Run := do
  validateId id
  let run ← readJson (ctx.directory id / "run.json")
  unless run.id == id do throw "Run manifest mismatch"
  return run

def Context.control (ctx : Context) (id : String) : Cli RunControl := do
  let path := ctx.directory id / "control.json"
  if ← request (.exists path) then readJson path else pure .active

private def Context.setControl (ctx : Context) (id : String) (state : RunControl) : Cli Unit :=
  saveJson (ctx.directory id / "control.json") state

def Context.allRuns (ctx : Context) : Cli (Array Run) := do
  unless ← request (.exists ctx.runs) do return #[]
  let mut runs := #[]
  for entry in ← request (.readDir ctx.runs) do
    if ← request (.exists (ctx.runs / entry / "run.json")) then
      runs := runs.push (← ctx.loadRun entry)
  return runs.qsort (fun a b => a.id < b.id)

def deploymentServices : Array String :=
  #["blobs", "scheduler-mailbox", "worker1-mailbox", "worker2-mailbox", "worker3-mailbox"]

def deploymentVolumes : Array String := #["scheduler-data", "blob-data",
  "scheduler-mailbox-data", "worker1-mailbox-data", "worker2-mailbox-data", "worker3-mailbox-data"]

def Context.configFile (ctx : Context) : Cli System.FilePath := do
  if ← request (.exists (Project.manifest ctx.root)) then
    pure (Project.assets ctx / "config.json") else pure (ctx.root / "deploy/config.json")

private def Context.startServices (ctx : Context) (verbose : Bool) : Cli Unit := do
  ctx.dockerLogged "services" "Starting blob and mailbox services"
    (#["compose", "-p", ctx.project, "-f", (← ctx.composeFile).toString,
      "--ansi", "never", "up", "-d", "--wait", "--no-build"] ++ deploymentServices) verbose

private def Context.checkVolumes (ctx : Context) : Cli Unit := do
  for volume in deploymentVolumes do
    let result ← docker #["volume", "inspect", ctx.project ++ "_" ++ volume] false
    unless result.exitCode == 0 do
      throw s!"Cannot verify volume {ctx.project}_{volume}. Use 'doctor'; restore missing data before resuming."

/-- Deployment checks must also work when every compute node is stopped or
uses the previous runtime protocol. The services/network must already be up.
This temporary reader executes no workflow and never opens scheduler storage. -/
private def Context.savedOutcome (ctx : Context) (image : String) (run : Run) : Cli (Option Exit) := do
  let legacyConfig := ctx.directory run.id / "config.json"
  let config ← if ← request (.exists legacyConfig) then pure legacyConfig else ctx.configFile
  let args := #["run", "--rm", "--network", ctx.project ++ "_default",
    "-v", s!"{config}:/etc/lean-cloud/config.json:ro",
    image, "outcome", "/etc/lean-cloud/config.json", run.id]
  let deadline := (← request .now) + 60000
  let mut waiting := false
  repeat
    let result ← docker args false
    if result.exitCode == 0 then
      return ← liftExcept (Json.parse result.stdout >>= fromJson?)
    let error := (result.stdout ++ result.stderr).trimAscii.toString
    let transient := [500, 502, 503, 504].any fun status =>
      (error.splitOn "\n").contains s!"S3 record read failed (HTTP {status})"
    unless transient && (← request .now) < deadline do throw (safe error)
    unless waiting do printLine "Waiting for blob storage to restore saved records…"
    waiting := true
    request (.sleep 1000)

/-- Stable containers belong to the deployment, independently of its runs. -/
def Context.node (ctx : Context) (role : String) : String := s!"{ctx.project}-{role}"

def Context.execApp (ctx : Context) (args : Array String) (input : Option String := none) : Cli String := do
  let output ← docker (#["exec"] ++ (if input.isSome then #["-i"] else #[]) ++
    #[ctx.node "scheduler", "cloud-app"] ++ args) (input := input)
  return output.stdout.trimAscii.toString

def Context.remote (ctx : Context) (run : Run) (command : String) : Cli String :=
  ctx.execApp #[command, "/etc/lean-cloud/config.json", run.id]

private def Context.startNodes (ctx : Context) (image : String) : Cli Unit := do
  let roles := #["scheduler", "worker1", "worker2", "worker3"]
  let mut existingNodes : Array String := #[]
  let mut replacing := false
  for role in roles do
    let name := ctx.node role
    let existing ← docker #["container", "inspect", name] false
    if existing.exitCode == 0 then
      let rows ← liftExcept (Json.parse existing.stdout >>= Json.getArr?)
      let row := rows[0]!
      let labels ← liftExcept (row.getObjVal? "Config" >>= (·.getObjVal? "Labels"))
      unless (labels.getObjValAs? String "lean-cloud.project").toOption == some ctx.project &&
          (labels.getObjValAs? String "lean-cloud.role").toOption == some role do
        throw s!"Container {name} is not a node of this deployment"
      existingNodes := existingNodes.push name
      replacing := replacing || (row.getObjValAs? String "Image").toOption != some image
  -- Never leave workers with the old code consuming the new pool's assignments.
  if replacing then
    discard <| docker (#["stop"] ++ existingNodes)
    discard <| docker (#["rm"] ++ existingNodes)
  for role in roles do
    let name := ctx.node role
    if !replacing && existingNodes.contains name then
      discard <| docker #["update", "--restart", "unless-stopped", name]
      discard <| docker #["start", name]
    else
      let extra := if role == "scheduler" then
        #["-v", ctx.project ++ "_scheduler-data:/data"] else #["-e", "CLOUD_WORKER_ID=" ++ role]
      let command := if role == "scheduler" then "serve-scheduler" else "serve-worker"
      discard <| docker (#["run", "-d", "--name", name, "--restart", "unless-stopped",
        "--label", "lean-cloud.project=" ++ ctx.project, "--label", "lean-cloud.role=" ++ role,
        "--log-opt", "max-size=10m", "--log-opt", "max-file=2", "--network", ctx.project ++ "_default",
        "-v", s!"{← ctx.configFile}:/etc/lean-cloud/config.json:ro"] ++ extra ++
        #[image, command, "/etc/lean-cloud/config.json"])

  discard <| ctx.execApp #["pool-health", "/etc/lean-cloud/config.json"]

def Context.deploy (ctx : Context) (executable : Option String := none) (verbose := false) : Cli Unit := do
  Deployments.remember ctx
  request (.createDir ctx.home)
  withLock (ctx.home / "deploy.lock") do
    if let some executable := executable then
      let app : Project.App := { name := ctx.project, executable }
      unless !executable.isEmpty && executable.toList.all (fun c =>
          c.toNat < 128 && (c.isAlphanum || c == '_')) do throw "Invalid Lake executable target"
      saveJson (Project.manifest ctx.root) app
    if ← request (.exists (Project.manifest ctx.root)) then Project.prepare ctx
    else unless ← request (.exists (ctx.root / "compose.yaml")) do
      throw "Use 'init DIRECTORY' for a new app, or 'deploy EXECUTABLE' for an existing app"
    let buildTag := ctx.project ++ "-app:build"
    let overlay := ctx.home / "build.json"
    saveJson overlay (Json.mkObj [("services", Json.mkObj [("worker", Json.mkObj [("image", toJson buildTag)])])])
    ctx.dockerLogged "build" "Building worker image"
      #["compose", "-p", ctx.project, "-f", (← ctx.composeFile).toString,
        "-f", overlay.toString, "--ansi", "never", "--progress", "plain", "build", "worker"] verbose
    let output ← docker #["image", "inspect", buildTag, "--format", "{{.Id}}"]
    let image := output.stdout.trimAscii.toString
    -- An ID alone is not a retention root in every Docker image store.
    -- Keep a versioned tag so rebuilding :build cannot discard an older run's image.
    discard <| docker #["tag", image, ctx.project ++ "-app:" ++ (image.drop 7 |>.toString)]
    let output ← docker #["run", "--rm", image, "programs"]
    let programs ← liftExcept (Json.parse output.stdout >>= fromJson? (α := Array ProgramInfo))
    unless !programs.isEmpty do throw "Application has no registered programs"
    let previous ← if ← request (.exists (ctx.home / "deployment.json")) then
        some <$> ctx.deployment else pure none
    if previous.isSome then ctx.checkVolumes
    -- down removes the network and compute containers, but retains the data.
    -- Bring only the services back before reading results or changing images.
    ctx.startServices verbose
    if let some previous := previous then
      if previous.image != image then
        for run in ← ctx.allRuns do
          let outcome ← ctx.savedOutcome image run
          unless outcome.isSome do
            throw s!"Finish or kill {run.id} before deploying a different image. Use 'up' if the previous deployment is down."
    discard <| docker #["volume", "create", ctx.project ++ "_scheduler-data"]
    saveJson (ctx.home / "deployment.json") (Deployment.mk ctx.project image programs)
    ctx.startNodes image
    printStyled (Styled.text s!"Deployed {programs.size} programs on 1 scheduler and 3 workers. Use 'run NAME' to submit a workflow." .green)
    printStyled (Styled.text s!"Logs: {ctx.home / "logs"}" .muted)

/-- Start existing services without rebuilding or silently replacing lost durable volumes. -/
def Context.up (ctx : Context) (verbose := false) : Cli Unit := do
  discard ctx.deployment
  Deployments.remember ctx
  withLock (ctx.home / "deploy.lock") do
    let deployment ← ctx.deployment
    unless ← request (.exists (← ctx.composeFile)) do throw "Deployment configuration is missing; use 'doctor'"
    unless ← request (.exists (← ctx.configFile)) do throw "Runtime configuration is missing; use 'doctor'"
    discard <| docker #["image", "inspect", deployment.image, "--format", "{{.Id}}"]
    ctx.checkVolumes
    ctx.startServices verbose
    ctx.startNodes deployment.image
    printStyled (Styled.text "Services and nodes are up. Active runs resume automatically. Use 'run NAME' to submit a workflow." .green)
    printStyled (Styled.text s!"Logs: {ctx.home / "logs"}" .muted)

/-- Stop actors before their services. Preserve volumes, images, and the run catalog. -/
def Context.down (ctx : Context) : Cli Unit := do
  request (.createDir ctx.home)
  withLock (ctx.home / "deploy.lock") do
    unless ← request (.exists (← ctx.composeFile)) do
      printLine "No deployment found."
      return
    printLine s!"Stopping {ctx.project}…"
    let output ← docker #["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project]
    let actors := output.stdout.splitOn "\n" |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty) |>.toArray
    if !actors.isEmpty then
      discard <| docker (#["stop"] ++ actors)
      discard <| docker (#["rm"] ++ actors)
    discard <| ctx.compose #["down", "--remove-orphans"]
    printStyled (Styled.text "Deployment stopped. Data is preserved. Use 'up' to restart the nodes and continue active runs." .yellow)

def Context.outcome (ctx : Context) (run : Run) : Cli (Option Exit) := do
  liftExcept (Json.parse (← ctx.remote run "outcome") >>= fromJson?)

def Context.scheduler (ctx : Context) (run : Run) : Cli Scheduler.State := do
  liftExcept (Json.parse (← ctx.remote run "status") >>= fromJson?)

/-- Idempotent recovery after interrupted launch. Existing definitions must agree. -/
def Context.resume (ctx : Context) (id : String) : Cli Unit := do
  let run ← ctx.loadRun id
  -- Serialize submission/control with deployment changes across consoles.
  withLock (ctx.home / "deploy.lock") do
  withLock (ctx.directory id / "launch.lock") do
    let control ← ctx.control id
    if control == .killed || control == .killing then
      throw s!"{id} was killed and cannot be resumed. Use 'kill {id}' to finish an interrupted cancellation."
    let inputPath := ctx.directory id / "input.json"
    let savedInput ← readJson (α := Json) inputPath
    unless savedInput.compress == run.input.compress do
      throw "Saved input differs from the immutable launch manifest"
    let deployment ← ctx.deployment
    unless deployment.image == run.image do throw "This run belongs to a different deployed image"
    discard <| ctx.execApp #["submit-entry", "/etc/lean-cloud/config.json", id, run.program.entry, "-"]
      (some (run.input.compress ++ "\n"))
    if (← ctx.outcome run).isSome then
      printLine s!"{id} is already completed. Use 'result {id}'."
      return
    discard <| ctx.remote run "resume"
    ctx.setControl id .active
    printStyled (Styled.text s!"Running {id} on the deployed pool. Use 'watch {id}' or 'inspect {id}'." .green)

def Context.pause (ctx : Context) (id : String) : Cli Unit := do
  let run ← ctx.loadRun id
  withLock (ctx.home / "deploy.lock") do
  withLock (ctx.directory id / "launch.lock") do
    let control ← ctx.control id
    if control == .killed || control == .killing then throw "A killed run cannot be paused"
    ctx.setControl id .pausing
    discard <| ctx.remote run "pause"
    ctx.setControl id .paused
    printStyled (Styled.text s!"Paused {id}. Use 'resume {id}' to continue from its replay records." .yellow)

def Context.kill (ctx : Context) (id : String) : Cli Unit := do
  let run ← ctx.loadRun id
  withLock (ctx.home / "deploy.lock") do
  withLock (ctx.directory id / "launch.lock") do
    ctx.setControl id .killing
    let outcome : Exit ← liftExcept (Json.parse (← ctx.remote run "cancel") >>= fromJson?)
    match outcome with
    | .cancelled _ =>
      ctx.setControl id .killed
      printStyled (Styled.text s!"Killed {id}. Its replay records are preserved; it cannot be resumed." .red)
    | _ =>
      ctx.setControl id .active
      printLine s!"{id} had already completed. Its result is unchanged; use 'result {id}'."

private def chooseProgram (programs : Array ProgramInfo) (name : String) : Except String ProgramInfo :=
  let found := programs.filter fun p => p.entry == name || (p.entry.splitOn "/").head! == name
  match found.toList with
  | [program] => .ok program
  | [] => .error s!"Unknown program: {name}"
  | _ => .error "Specify the program version (name/version)"

def Context.launch (ctx : Context) (name : String) (file : Option String) (id : Option String) : Cli Unit := do
  let deployment ← ctx.deployment
  let program ← liftExcept (chooseProgram deployment.programs name)
  let input ← match file, program.sampleInput with
    | some file, _ => readJson (α := Json) (ctx.root / file)
    | none, some sample => pure sample
    | none, none => throw "This program needs --input FILE.json"
  let id := id.getD s!"run-{← request .pid}-{← request .now}"
  validateId id
  discard <| ctx.execApp #["validate", program.entry] (some (input.compress ++ "\n"))
  request (.createDir ctx.runs)
  withLock (ctx.home / "catalog.lock") do
    let directory := ctx.directory id
    if ← request (.exists (directory / "run.json")) then
      throw s!"Run {id} already exists; use 'resume {id}'"
    request (.createDir directory)
    saveJson (directory / "input.json") input
    saveJson (directory / "run.json") (Run.mk id deployment.image program input)
  ctx.resume id

end LeanCloudCli
