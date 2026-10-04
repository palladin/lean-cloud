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
    ctx.startServices verbose
    discard <| docker #["volume", "create", ctx.project ++ "_scheduler-data"]
    saveJson (ctx.home / "deployment.json") (Deployment.mk ctx.project image programs)
    printStyled (Styled.text s!"Deployed {programs.size} programs. Use 'programs' to list them, then 'run NAME'." .green)
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
    for volume in deploymentVolumes do
      let result ← docker #["volume", "inspect", ctx.project ++ "_" ++ volume] false
      unless result.exitCode == 0 do
        throw s!"Cannot verify volume {ctx.project}_{volume}. Use 'doctor'; restore missing data before resuming."
    ctx.startServices verbose
    printStyled (Styled.text "Services are up. Use 'resume RUN' for an unfinished run, or 'run NAME' for a new one." .green)
    printStyled (Styled.text s!"Logs: {ctx.home / "logs"}" .muted)

def Context.container (ctx : Context) (run : Run) (role : String) : String :=
  s!"{ctx.project}-{run.id}-{role}"

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
    printStyled (Styled.text "Deployment stopped. Data is preserved. Use 'up', then 'resume RUN' to continue a run." .yellow)

def Context.mounts (ctx : Context) (run : Run) : Array String :=
  #["--network", ctx.project ++ "_default", "-v", s!"{ctx.directory run.id / "config.json"}:/etc/lean-cloud/config.json:ro"]

def Context.remote (ctx : Context) (run : Run) (command : String) : Cli String := do
  let output ← docker (#["run", "--rm"] ++ ctx.mounts run ++
    #[run.image, command, "/etc/lean-cloud/config.json", run.id])
  return output.stdout.trimAscii.toString

def Context.outcome (ctx : Context) (run : Run) : Cli (Option Exit) := do
  liftExcept (Json.parse (← ctx.remote run "outcome") >>= fromJson?)

def Context.scheduler (ctx : Context) (run : Run) : Cli Scheduler.State := do
  liftExcept (Json.parse (← ctx.remote run "status") >>= fromJson?)

private def Context.startContainer (ctx : Context) (run : Run) (role : String) (args : Array String) : Cli Unit := do
  let name := ctx.container run role
  let existing ← docker #["container", "inspect", name] false
  if existing.exitCode == 0 then
    let rows ← liftExcept (Json.parse existing.stdout >>= Json.getArr?)
    let row := rows[0]!
    let labels ← liftExcept ((row.getObjVal? "Config") >>= (·.getObjVal? "Labels"))
    unless (labels.getObjValAs? String "lean-cloud.run").toOption == some run.id &&
        (labels.getObjValAs? String "lean-cloud.project").toOption == some ctx.project &&
        (row.getObjValAs? String "Image").toOption == some run.image do
      throw s!"Container {name} does not belong to this run/image"
    discard <| docker #["update", "--restart", "on-failure", name]
    discard <| docker #["start", name]
  else
    let extra := if role == "scheduler" then
      #["-v", ctx.project ++ "_scheduler-data:/data"]
      else #["-e", "CLOUD_WORKER_ID=" ++ role]
    discard <| docker (#["run", "-d", "--name", name, "--restart", "on-failure",
      "--label", "lean-cloud.project=" ++ ctx.project, "--label", "lean-cloud.run=" ++ run.id,
      "--label", "lean-cloud.role=" ++ role, "--log-opt", "max-size=10m", "--log-opt", "max-file=2"] ++
      ctx.mounts run ++ extra ++ #[run.image] ++ args)

/-- Idempotent recovery after interrupted launch. Existing definitions must agree. -/
def Context.resume (ctx : Context) (id : String) : Cli Unit := do
  let run ← ctx.loadRun id
  -- Serialize container startup with deployment and shutdown across consoles.
  withLock (ctx.home / "deploy.lock") do
  withLock (ctx.directory id / "launch.lock") do
    let control ← ctx.control id
    if control == .killed || control == .killing then
      throw s!"{id} was killed and cannot be resumed. Use 'kill {id}' to finish an interrupted cancellation."
    let inputPath := ctx.directory id / "input.json"
    let savedInput ← readJson (α := Json) inputPath
    unless savedInput.compress == run.input.compress do
      throw "Saved input differs from the immutable launch manifest"
    discard <| docker (#["run", "--rm"] ++ ctx.mounts run ++
      #["-v", s!"{inputPath}:/input.json:ro", run.image, "submit-entry", "/etc/lean-cloud/config.json", run.id, run.program.entry, "/input.json"])
    if (← ctx.outcome run).isSome then
      printLine s!"{id} is already completed. Use 'result {id}'."
      return
    -- Clear paused intent before any actor starts. An interrupted startup can
    -- be repaired by resume, but must not still be presented as a stopped run.
    ctx.setControl id .active
    ctx.startContainer run "scheduler" #["scheduler", "/etc/lean-cloud/config.json", id]
    -- Consumer reconnects are handled by the ordinary process restart policy.
    for worker in ["worker1", "worker2", "worker3"] do
      ctx.startContainer run worker #["worker", "/etc/lean-cloud/config.json", id]
    printStyled (Styled.text s!"Started {id}. Use 'watch {id}' or 'inspect {id}'." .green)

/-- Stop only this run's actors. Restart is disabled before stopping any actor;
the services, replay records, broker messages and scheduler database survive. -/
private def Context.stopRun (ctx : Context) (run : Run) : Cli Unit := do
  let output ← docker #["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project,
    "--filter", "label=lean-cloud.run=" ++ run.id]
  let actors := output.stdout.splitOn "\n" |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty) |>.toArray
  unless actors.isEmpty do
    discard <| docker (#["update", "--restart", "no"] ++ actors)
    discard <| docker (#["stop", "--time", "0"] ++ actors)

def Context.pause (ctx : Context) (id : String) : Cli Unit := do
  let run ← ctx.loadRun id
  withLock (ctx.home / "deploy.lock") do
  withLock (ctx.directory id / "launch.lock") do
    let control ← ctx.control id
    if control == .killed || control == .killing then throw "A killed run cannot be paused"
    ctx.setControl id .pausing
    ctx.stopRun run
    ctx.setControl id .paused
    printStyled (Styled.text s!"Paused {id}. Use 'resume {id}' to continue from its replay records." .yellow)

def Context.kill (ctx : Context) (id : String) : Cli Unit := do
  let run ← ctx.loadRun id
  withLock (ctx.home / "deploy.lock") do
  withLock (ctx.directory id / "launch.lock") do
    ctx.setControl id .killing
    ctx.stopRun run
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
  discard <| docker #["run", "--rm", "-i", deployment.image, "validate", program.entry]
    (input := some (input.compress ++ "\n"))
  request (.createDir ctx.runs)
  withLock (ctx.home / "catalog.lock") do
    let directory := ctx.directory id
    if ← request (.exists (directory / "run.json")) then
      throw s!"Run {id} already exists; use 'resume {id}'"
    request (.createDir directory)
    let configPath ← ctx.configFile
    let config ← readJson (α := Json) configPath
    let scheduler ← liftExcept (config.getObjVal? "scheduler")
    let config := config.setObjVal! "scheduler"
      (scheduler.setObjVal! "database" (toJson s!"/data/console-{id}.sqlite"))
    saveJson (directory / "config.json") config
    saveJson (directory / "input.json") input
    saveJson (directory / "run.json") (Run.mk id deployment.image program input)
  ctx.resume id

end LeanCloudCli
