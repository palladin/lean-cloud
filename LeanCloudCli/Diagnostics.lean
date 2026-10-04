import LeanCloudCli.Monitor

namespace LeanCloudCli
open Lean

def serviceState (nodes : Array Node) (service : String) : String :=
  match nodes.find? (fun node => node.run.isNone && node.role == service) with
  | none => "absent"
  | some node => if node.state == "running" then
      node.health.getD "running (health unknown)" else node.state

def deploymentState (nodes : Array Node) (workers := defaultWorkerCount) : String :=
  if nodes.isEmpty then "down"
  else if (deploymentServices workers).all (fun name => serviceState nodes name == "healthy") then "up"
  else if nodes.all (·.state != "running") then "stopped"
  else "partial / check status"

def listDeployments (ctx : Context) : Cli Unit := do
  Deployments.discover ctx
  let catalog ← Deployments.load
  printHeading "  DEPLOYMENT                    STATE                     DIRECTORY"
  for entry in catalog.entries.qsort (fun a b => a.project < b.project) do
    let target := entry.context
    let state ← if !(← request (.isDir target.root)) then pure "directory missing"
      else if !(← request (.exists (target.home / "deployment.json"))) then pure "not deployed"
      else try pure (deploymentState (← target.nodes) (← target.deployment).workers) catch _ => pure "Docker unavailable"
    let marker := if entry.project == ctx.project && entry.root == ctx.root.toString then "* " else "  "
    printStyled (Styled.text (marker ++ pad 30 entry.project) (if marker == "* " then .selected else .cyan) ++
      Styled.text (pad 26 state) (Styled.statusColor state) ++ Styled.text entry.root)
  if catalog.entries.isEmpty then printLine "No known deployments. Use 'deploy' or 'open DIRECTORY'."
  printLine "* selected · local catalog for the current Docker context"

def Context.status (ctx : Context) : Cli Unit := do
  printHeading s!"Deployment: {safe ctx.project}"
  printLine s!"Directory:  {safe ctx.root.toString}"
  let deployment ← ctx.deployment
  printLine s!"Image:      {safe deployment.image}"
  printLine s!"Workers:    {deployment.workers} desired; use 'scale N' to change capacity"
  printLine s!"Programs:   {deployment.programs.size}"
  printLine s!"Runs:       {(← ctx.allRuns).size} recorded; use 'ps' for workflow results"
  let nodes ← try ctx.nodes catch _ => throw "Docker unavailable; use 'doctor' to diagnose connectivity"
  printStyled (Styled.text "Services:   " ++ Styled.text (deploymentState nodes deployment.workers) (Styled.statusColor (deploymentState nodes deployment.workers)))
  for service in deploymentServices deployment.workers do
    printStyled (Styled.text ("  " ++ pad 22 service) .cyan ++
      Styled.text (serviceState nodes service) (Styled.statusColor (serviceState nodes service)))
  let actors := nodes.filter (fun node => isActor node.role)
  printLine s!"Actors:     {(actors.filter (·.state == "running")).size} running / {actors.size} containers"
  if nodes.isEmpty then printLine "Use 'up' to start the node pool and recover active runs."

private def check (label : String) (action : Cli Unit) : Cli Bool := do
  let result ← observing action
  match result with
  | .ok () => printStyled (Styled.text "[ok]   " .green ++ Styled.text label); return true
  | .error error => printStyled (Styled.text "[fail] " .red ++ Styled.text s!"{label}: {safe error}"); return false

private def checkProcess (args : Array String) (hint : String) : Cli Unit := do
  let result ← docker args false
  unless result.exitCode == 0 do throw hint

/-- Read-only host and deployment diagnostics. Health checks are not end-to-end probes. -/
def Context.doctor (ctx : Context) : Cli Unit := do
  printHeading s!"Checking {safe ctx.project}…"
  let mut failures := 0
  let record (passed : Bool) := if passed then 0 else 1
  failures := failures + record (← check "Deployment catalog" (discard Deployments.load))
  failures := failures + record (← check "Application directory" do
    unless ← request (.isDir ctx.root) do throw "Directory is missing; use 'open DIRECTORY'")
  failures := failures + record (← check "Runtime configuration (JSON structure)" do
    let config ← readJson (α := Json) (← ctx.configFile)
    for key in ["scheduler", "mailboxes", "blobs"] do
      discard <| liftExcept (config.getObjVal? key >>= Json.getObj?))
  let deployed ← observing ctx.deployment
  failures := failures + record (← check "Deployment manifest" (discard (liftExcept deployed)))
  let cli ← check "Docker CLI" (checkProcess #["--version"] "Install Docker")
  failures := failures + record cli
  let compose ← if cli then check "Docker Compose" (checkProcess #["compose", "version"] "Install the Compose plugin")
    else pure false
  if cli then failures := failures + record compose
  if compose then
    failures := failures + record (← check "Compose configuration" do
      unless ← request (.exists (← ctx.composeFile)) do throw "Configuration is missing; use 'deploy'"
      checkProcess #["compose", "-p", ctx.project, "-f", (← ctx.composeFile).toString, "config", "--quiet"]
        "Compose configuration is invalid; inspect the deployment files")
  let daemon ← if cli then check "Docker daemon" (checkProcess #["info", "--format", "{{.ServerVersion}}"]
    "Start Docker and check your Docker context") else pure false
  if cli then failures := failures + record daemon
  if daemon then
    if let .ok deployment := deployed then
      let runs ← observing ctx.allRuns
      failures := failures + record (← check "Run catalog" (discard (liftExcept runs)))
      let images := (runs.toOption.getD #[]).foldl (fun images run =>
        if images.contains run.image then images else images.push run.image) #[deployment.image]
      for image in images do
        failures := failures + record (← check s!"Image {safe image}" (checkProcess
          #["image", "inspect", image, "--format", "{{.Id}}"]
          "Saved image is unavailable; restore it before resuming existing runs"))
      for volume in deploymentVolumes deployment.retainedCount do
        failures := failures + record (← check s!"Volume {volume}" (checkProcess
          #["volume", "inspect", ctx.project ++ "_" ++ volume]
          "Cannot access durable volume; verify Docker context and restore missing data"))
      let inventory ← observing ctx.nodes
      failures := failures + record (← check "Container inventory" (discard (liftExcept inventory)))
      if let .ok nodes := inventory then
        for service in deploymentServices deployment.workers do
          failures := failures + record (← check service do
            let state := serviceState nodes service
            unless state == "healthy" do
              throw s!"{state}; use 'up' for stopped services or inspect the service's Docker logs")
        for node in nodes.filter (fun node => isActor node.role) do
          if node.state != "running" then
            printStyled (Styled.text s!"[note] {safe node.name}: {safe node.state}; check 'ps' before resuming" .yellow)
  printLine "Checks cover local files, images, volumes and container health; runtime credentials and workflow execution are not probed."
  unless failures == 0 do throw s!"Doctor found {failures} failed check(s)."
  printStyled (Styled.text "All checks passed." .green)

end LeanCloudCli
