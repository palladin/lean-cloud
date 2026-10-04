import LeanCloudCli.Diagnostics
import LeanCloudCli.Top
import LeanCloudCli.Help
import LeanCloudCli.Watch

namespace LeanCloudCli
open Lean LeanCloud

private def exitLabel : Exit → String
  | .success _ => "completed"
  | .failure _ => "failed"
  | .cancelled _ => "cancelled"

private def inspectRun (ctx : Context) (id : String) : Cli Unit := do
  let run ← ctx.loadRun id
  printHeading s!"{run.id}  {run.program.entry}"
  let control ← ctx.control id
  let outcome ← try ctx.outcome run catch error =>
    if control != .active then pure none else throw error
  if let some outcome := outcome then
    printStyled (Styled.text "Outcome: " ++ Styled.text (exitLabel outcome) (Styled.statusColor (exitLabel outcome)))
  if control != .active then
    if outcome.isNone then printStyled (Styled.text "Status: " ++ Styled.text control.label (Styled.statusColor control.label))
    return
  let state ← try pure (some (← ctx.scheduler run)) catch error =>
    if outcome.isSome then pure none else throw error
  let some state := state | return
  printHeading "LOCATION             STATUS       WORKER      ATTEMPT"
  for job in state.jobs do
    let (status, worker, attempt) := match job.status with
      | .pending => ("pending", "—", "—")
      | .waiting children => (s!"join ({children.size})", "—", "—")
      | .done => ("done", "—", "—")
      | .running worker attempt _ => ("running", worker, toString attempt)
    printStyled (Styled.text (pad 21 job.location.key) .cyan ++
      Styled.text (pad 13 status) (Styled.statusColor status) ++ Styled.text s!"{pad 12 worker}{attempt}")
  if let some error := state.error then printLine s!"Scheduler error: {safe error.message}"

private def listRuns (ctx : Context) : Cli Unit := do
  printHeading "RUN                            PROGRAM                  STATUS"
  for run in ← ctx.allRuns do
    let status ← try
      match ← ctx.outcome run with
      | some outcome => pure (exitLabel outcome)
      | none =>
        let control ← ctx.control run.id
        if control != .active then pure control.label else do
          let state ← ctx.scheduler run
          pure (if state.error.isSome then "scheduler error" else
            s!"running ({(state.jobs.filter (·.status == .done)).size}/{state.jobs.size})")
    catch _ =>
      let control ← ctx.control run.id
      pure (if control != .active then control.label else "unavailable / launch incomplete")
    printStyled (Styled.text (pad 31 run.id) .cyan ++ Styled.text (pad 25 run.program.entry) ++
      Styled.text status (Styled.statusColor status))

private def showNodes (ctx : Context) : Cli Unit := do
  let nodes ← ctx.nodes
  let values ← samples nodes
  printHeading "NODE                                STATE      CPU                     MEMORY"
  for node in nodes do
    let value := values.find? (·.1 == node.name)
    let cpu := value.map (fun (_, s) => percent s.cpu) |>.getD "—"
    let memory := value.map (fun (_, s) => humanBytes s.memory) |>.getD "—"
    let cpuBar := value.map (fun (_, s) => meter s.cpu 100000 10) |>.getD (Styled.text "[unavailable]" .muted)
    let memBar := value.map (fun (_, s) => meter s.memory s.limit 10) |>.getD (Styled.text "[unavailable]" .muted)
    printStyled (Styled.text (pad 36 node.name) .cyan ++
      Styled.text (pad 11 node.state) (Styled.statusColor node.state) ++ cpuBar ++
      Styled.text (" " ++ pad 10 cpu) ++ memBar ++ Styled.text (" " ++ memory))

/-- Reject malformed flags before deployment changes any files or services. -/
private def deploymentOptions (args : List String) (allowExecutable : Bool)
  : Except String (Option String × Bool × Option Nat) := do
  let usage := if allowExecutable then "Usage: deploy [EXECUTABLE] [--workers N] [-v|--verbose]"
    else "Usage: up [-v|--verbose]"
  let mut executable := none
  let mut verbose := false
  let mut workers := none
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--workers" :: value :: tail =>
      unless allowExecutable do throw usage
      if workers.isSome then throw "Duplicate --workers"
      let some count := value.toNat? | throw "Worker count must be a nonnegative integer"
      workers := some count; rest := tail
    | arg :: tail =>
      if arg == "-v" || arg == "--verbose" then
        if verbose then throw "Duplicate verbose flag (-v/--verbose)"
        verbose := true
      else if allowExecutable && executable.isNone && !arg.startsWith "-" then
        executable := some arg
      else throw usage
      rest := tail
    | [] => pure ()
  return (executable, verbose, workers)

private def runOptions (args : List String) : Except String (Option String × Option String) := do
  let mut file := none
  let mut id := none
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--input" :: value :: tail =>
      if file.isSome then throw "Duplicate --input"
      file := some value; rest := tail
    | "--id" :: value :: tail =>
      if id.isSome then throw "Duplicate --id"
      id := some value; rest := tail
    | _ => throw "Usage: run PROGRAM [--input FILE.json] [--id ID]"
  return (file, id)

def command (ctx : Context) (args : List String) : Cli Bool := do
  if Help.requested args then
    Help.display args
    return true
  match args with
  | [] => return true
  | ["quit"] | ["exit"] => return false
  | "deploy" :: options =>
    let (executable, verbose, workers) ← liftExcept (deploymentOptions options true)
    ctx.deploy executable verbose workers
  | ["scale", value] =>
    let some count := value.toNat? | throw "Usage: scale N (a nonnegative integer)"
    ctx.scale count
  | ["down"] => ctx.down
  | "up" :: options =>
    let (_, verbose, _) ← liftExcept (deploymentOptions options false)
    ctx.up verbose
  | ["deployments"] => listDeployments ctx
  | ["status"] => ctx.status
  | ["doctor"] => ctx.doctor
  | ["init", directory] => Project.init ctx directory
  | ["init", directory, "--sdk", path] => Project.init ctx directory (some path)
  | ["programs"] =>
    printHeading "PROGRAM                  DESCRIPTION"
    for program in (← ctx.deployment).programs do
      printStyled (Styled.text (pad 25 program.entry) .cyan ++ Styled.text program.description)
  | "run" :: name :: args =>
    let (file, id) ← liftExcept (runOptions args)
    ctx.launch name file id
  | ["ps"] => listRuns ctx
  | ["inspect", id] => inspectRun ctx id
  | ["nodes"] => showNodes ctx
  | ["top"] => Top.run ctx
  | ["top", "--once"] => Top.run ctx true
  | ["resume", id] => ctx.resume id
  | ["pause", id] => ctx.pause id
  | ["kill", id] => ctx.kill id
  | ["watch", id] => Watch.run ctx id
  | ["watch", id, "--once"] => Watch.run ctx id true
  | ["result", id] =>
    let run ← ctx.loadRun id
    let some outcome ← ctx.outcome run | printLine "pending"; return true
    match outcome with
    | .success value =>
      if run.program.resultSchema == (inferInstance : Codec BlobRef).schema then
        printLine (safe (← ctx.remote run "result"))
      else printLine (safe value.pretty)
    | .failure error => printLine s!"failed: {safe error.message}"
    | .cancelled reason => printLine s!"cancelled: {safe reason}"
  | ["logs", id] | ["logs", id, _] =>
    let role := args[2]?.getD "worker1"
    unless isActor role do throw "Unknown actor"
    let run ← ctx.loadRun id
    let output ← docker #["logs", "--tail", "100", ctx.node role]
    for line in (output.stdout ++ output.stderr).splitOn "\n" do
      if let some event := event? line then
        if event.run == run.id then printLine (safe line)
  | _ => throw "Unknown command. Use 'help'."
  return true

/-- Project selection belongs to the CLI state, not the process's working directory. -/
def dispatch (ctx : Context) (args : List String) : Cli (Context × Bool) := do
  if Help.requested args then return (ctx, ← command ctx args)
  match args with
  | ["use", name] =>
    unless (← Deployments.load).entries.any (·.project == name) do Deployments.discover ctx
    let selected ← Deployments.select name
    printLine s!"Selected {safe selected.project} at {safe selected.root.toString}"
    return (selected, true)
  | ["open", directory] =>
    let selected ← Project.openDirectory ctx directory
    Deployments.remember selected
    return (selected, true)
  | ["init", directory] | ["init", directory, "--sdk", _] =>
    discard (command ctx args)
    let selected ← Project.openDirectory ctx directory
    Deployments.remember selected
    return (selected, true)
  | _ => return (ctx, ← command ctx args)

end LeanCloudCli
