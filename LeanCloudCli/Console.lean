import LeanCloudCli.Diagnostics
import LeanCloudCli.Top
import LeanCloudCli.Help
import LeanCloudCli.Watch
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
    if outcome.isNone then printStyled (Styled.text "Status: " ++ Styled.text (controlLabel control) (Styled.statusColor (controlLabel control)))
  let state ← try pure (some (← ctx.observation run)) catch error =>
    if outcome.isSome || control != .active then pure none else throw error
  let some state := state | return
  if let some diagnostics := state.diagnostics then
    printLine s!"Execution: {phaseLabel diagnostics.phase}"
    printLine s!"Assignments: {diagnostics.pending} pending, {diagnostics.running} running, {diagnostics.replies} replies collected"
    if diagnostics.configuredWorkers == some 0 then printLine "No workers configured. Add capacity using your deployment tooling."
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
        else if control != .active then pure (controlLabel control) else do
          let state ← liftExcept observed
          pure (if state.error.isSome then "scheduler error" else
            s!"running ({(state.jobs.filter (·.status == .done)).size}/{state.jobs.size})")
    catch _ =>
      if (observed.toOption.bind (·.diagnostics)).any (·.phase == .stopping) then
        pure (phaseShortLabel .stopping)
      else do
        let control ← ctx.control run.id
        pure (if control != .active then (controlLabel control) else "unavailable / launch incomplete")
    let span := timing >>= (·.span)
    let started := span.map (Time.stamp ∘ Timing.Span.startedMs) |>.getD "—"
    let finished := (span >>= (·.finishedMs)).map Time.stamp |>.getD "—"
    let elapsed := Time.elapsed span (timing.map (·.observedMs) |>.getD 0)
    printStyled (Styled.text (pad 31 run.id) .cyan ++ Styled.text (pad 25 run.program.entry) ++
      Styled.text (pad 22 status) (Styled.statusColor status) ++
      Styled.text s!"{pad 21 started}{pad 21 finished}" .muted ++ Styled.text elapsed .cyan)

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
  | ["remove", id] => ctx.removeRun id
  | ["connections"] => listConnections ctx
  | ["status"] => ctx.status
  | ["doctor"] => ctx.doctor
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
        printLine (safe (← ctx.result run))
      else printLine (safe value.pretty)
    | .failure error => printLine s!"failed: {safe error.message}"
    | .cancelled reason => printLine s!"cancelled: {safe reason}"
  | ["logs", id] | ["logs", id, _] =>
    let run ← ctx.loadRun id
    let snapshot ← Trace.load ctx run
    for step in snapshot.steps do
      if args[2]?.all (· == step.event.worker) then
        printLine (safe s!"{step.timestamp} {step.event.worker} {step.event.location} {step.event.activity} {step.event.operation}")
    unless snapshot.warning.isEmpty do printLine (safe snapshot.warning)
  | _ => throw "Unknown command. Use 'help'."
  return true

/-- Connection selection changes only the console's local profile. -/
def dispatch (ctx : Context) (args : List String) : Cli (Context × Bool) := do
  if Help.requested args then return (ctx, ← command ctx args)
  match args with
  | ["connect", name, url] | ["connect", name, url, "--token-env", _] |
      ["connect", name, url, "--token-file", _] =>
    let tokenFile ← if args[3]? == some "--token-file" then
      pure (some ((← request .currentDir) / args[4]!).toString) else pure none
    let tokenEnv := if args[3]? == some "--token-env" then args[4]! else "LEAN_CLOUD_TOKEN"
    let selected ← Connections.connect name url tokenEnv tokenFile
    discard selected.deployment
    discard selected.allRuns
    printLine s!"Connected to {safe selected.project}. Use 'programs' or 'ps'."
    return (selected, true)
  | ["use", name] =>
    let selected ← Profiles.select name
    printLine s!"Selected {safe selected.project}"
    return (selected, true)
  | _ => return (ctx, ← command ctx args)

end LeanCloudCli
