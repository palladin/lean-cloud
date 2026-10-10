import LeanCloudCli.Diagnostics
import LeanCloudCli.Top
import LeanCloudCli.Help
import LeanCloudCli.Watch
import LeanCloudCli.Clean
import LeanCloudCli.Backup
import LeanCloudCli.Time

namespace LeanCloudCli
open Lean LeanCloud

private def exitLabel : Exit → String
  | .success _ => "completed"
  | .failure _ => "failed"
  | .cancelled _ => "cancelled"

def phaseLabel : Pool.Phase → String
  | .completed => "completed"
  | .failed => "failed"
  | .killed => "killed"
  | .paused => "paused"
  | .stopping => "waiting for workers to stop"
  | .finalizing => "publishing terminal result"
  | .noWorkers => "waiting for workers"
  | .queued => "waiting for assignment"
  | .running => "running"

def phaseShortLabel : Pool.Phase → String
  | .stopping => "waiting for stop"
  | .finalizing => "publishing result"
  | .queued => "pending assignment"
  | phase => phaseLabel phase

private def inspectRun (ctx : Context) (id : String) : Cli Unit := do
  let run ← ctx.loadRun id
  printHeading s!"{run.id}  {run.program.entry}"
  let control ← ctx.control id
  let outcome ← try ctx.outcome run catch error =>
    if control != .active then pure none else throw error
  if let some outcome := outcome then
    printStyled (Styled.text "Outcome: " ++ Styled.text (exitLabel outcome) (Styled.statusColor (exitLabel outcome)))
    if let .failure error := outcome then printLine s!"Error: {safe error.message}"
  if control != .active then
    if outcome.isNone then printStyled (Styled.text "Status: " ++ Styled.text control.label (Styled.statusColor control.label))
  let state ← try pure (some (← ctx.observation run)) catch error =>
    if outcome.isSome || control != .active then pure none else throw error
  let some state := state | return
  if let some diagnostics := state.diagnostics then
    printLine s!"Execution: {phaseLabel diagnostics.phase}"
    printLine s!"Assignments: {diagnostics.pending} pending, {diagnostics.running} running, {diagnostics.replies} replies collected"
    if diagnostics.configuredWorkers == some 0 then printLine "No workers configured. Use 'scale N' to add capacity."
    unless diagnostics.stopping.isEmpty do
      printLine s!"Waiting for stop acknowledgement: {String.intercalate ", " diagnostics.stopping.toList}"
  let traces ← Trace.load ctx run
  for job in state.jobs do
    if let .running worker attempt _ := job.status then
      let latest := traces.steps.toList.reverse.find? fun step =>
        step.event.worker == worker && step.event.attempt == some attempt
      if let some step := latest then
        if step.event.activity == "retrying" then
          printLine s!"{safe worker}: {safe step.event.operation} after an IO/transport failure (last observation)"
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
  printHeading s!"{pad 31 "RUN"}{pad 25 "PROGRAM"}{pad 22 "STATUS"}{pad 21 "STARTED (UTC)"}{pad 21 "FINISHED (UTC)"}ELAPSED"
  for run in ← ctx.allRuns do
    let observed ← observing (ctx.observation run)
    let timing ← match observed with
      | .ok state => pure state.timing
      | .error _ => ctx.savedTiming run
    let status ← try
      match ← ctx.outcome run with
      | some outcome => pure (exitLabel outcome)
      | none =>
        let control ← ctx.control run.id
        if let some diagnostics := observed.toOption.bind (·.diagnostics) then
          pure (phaseShortLabel diagnostics.phase)
        else if control != .active then pure control.label else do
          let state ← liftExcept observed
          pure (if state.error.isSome then "scheduler error" else
            s!"running ({(state.jobs.filter (·.status == .done)).size}/{state.jobs.size})")
    catch _ =>
      if (observed.toOption.bind (·.diagnostics)).any (·.phase == .stopping) then
        pure (phaseShortLabel .stopping)
      else do
        let control ← ctx.control run.id
        pure (if control != .active then control.label else "unavailable / launch incomplete")
    let span := timing >>= (·.span)
    let started := span.map (Time.stamp ∘ Timing.Span.startedMs) |>.getD "—"
    let finished := (span >>= (·.finishedMs)).map Time.stamp |>.getD "—"
    let elapsed := Time.elapsed span (timing.map (·.observedMs) |>.getD 0)
    printStyled (Styled.text (pad 31 run.id) .cyan ++ Styled.text (pad 25 run.program.entry) ++
      Styled.text (pad 22 status) (Styled.statusColor status) ++
      Styled.text s!"{pad 21 started}{pad 21 finished}" .muted ++ Styled.text elapsed .cyan)

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
  | ["clean"] => ctx.clean
  | ["remove", id] => ctx.removeRun id
  | ["backup", directory] => Backup.save ctx directory
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
  | ["restore", directory] => return (← Backup.restore ctx.root directory, true)
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
