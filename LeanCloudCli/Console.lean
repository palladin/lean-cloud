import LeanCloudCli.Diagnostics

namespace LeanCloudCli
open Lean LeanCloud

private def exitLabel : Exit → String
  | .success _ => "completed"
  | .failure _ => "failed"
  | .cancelled _ => "cancelled"

private def inspectRun (ctx : Context) (id : String) : Cli Unit := do
  let run ← ctx.loadRun id
  printLine s!"{run.id}  {run.program.entry}"
  let control ← ctx.control id
  let outcome ← try ctx.outcome run catch error =>
    if control != .active then pure none else throw error
  if let some outcome := outcome then printLine s!"Outcome: {exitLabel outcome}"
  if control != .active then
    if outcome.isNone then printLine s!"Status: {control.label}"
    return
  let state ← try pure (some (← ctx.scheduler run)) catch error =>
    if outcome.isSome then pure none else throw error
  let some state := state | return
  printLine "LOCATION             STATUS       WORKER      ATTEMPT"
  for job in state.jobs do
    let (status, worker, attempt) := match job.status with
      | .pending => ("pending", "—", "—")
      | .waiting children => (s!"join ({children.size})", "—", "—")
      | .done => ("done", "—", "—")
      | .running worker attempt _ => ("running", worker, toString attempt)
    printLine s!"{pad 21 job.location.key}{pad 13 status}{pad 12 worker}{attempt}"
  if let some error := state.error then printLine s!"Scheduler error: {safe error.message}"

private def listRuns (ctx : Context) : Cli Unit := do
  printLine "RUN                            PROGRAM                  STATUS"
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
    printLine s!"{pad 31 run.id}{pad 25 run.program.entry}{status}"

private def showNodes (ctx : Context) : Cli Unit := do
  let nodes ← ctx.nodes
  let values ← samples nodes
  printLine "NODE                                          STATE      CPU        MEMORY"
  for node in nodes do
    let value := values.find? (·.1 == node.name)
    let cpu := value.map (fun (_, s) => percent s.cpu) |>.getD "—"
    let memory := value.map (fun (_, s) => humanBytes s.memory) |>.getD "—"
    printLine s!"{pad 46 node.name}{pad 11 node.state}{pad 11 cpu}{memory}"

private def lastEvent (events : Array ExecutionEvent) : Option ExecutionEvent := events.back?

private def sourceStart (run : Run) (events : Array (String × Array ExecutionEvent)) : Nat :=
  match run.program.source with
  | none => 1
  | some source =>
    let observed := events.findSome? fun (_, trace) => do
      let event ← lastEvent trace
      let site ← source.sites.find? (·.operation == event.operation)
      return site.line
    max 1 (observed.getD ((source.sites[0]?.map (·.line)).getD 1) - 1)

/-- A compact terminal frame. Source markers are observations, not a debugger PC. -/
def frame (ctx : Context) (run : Run) (nodes : Array Node)
    (events : Array (String × Array ExecutionEvent)) (histories : Array History)
    (selected sourceOffset width height : Nat) (status := "") (disk : Option String := none) : Array String := Id.run do
  let selectedNode := nodes[selected % max 1 nodes.size]?
  let mut lines := #[s!"lean-cloud  {run.id}  {run.program.entry}  {status}", "q: back · last observed · Tab: node · 1/2/3: worker · j/k: source · a: auto"]
  for (worker, trace) in events do
    let node := nodes.find? (·.name == ctx.container run worker)
    let state := node.map (·.state) |>.getD "absent"
    let detail := match lastEvent trace with
      | none => "no execution event"
      | some e => s!"a{e.attempt.getD 0}  {e.location}  {e.activity} {e.operation}"
    lines := lines.push s!"{worker} [{state}] {detail}"
  let graph := match selectedNode with
    | none => #["No nodes"]
    | some node =>
      let history := histories.find? (fun h => h.name == node.name && h.fresh && h.points.back?.map (·.session) == some node.started)
      #[s!"Node: {node.name}", s!"State: {node.state}"] ++
        (if node.state == "running" then metricLines (history.map (·.points) |>.getD #[])
         else #["No live samples; process is stopped"]) ++ disk.toArray
  let available := max 4 (height - lines.size - 3)
  let codeRows := if width ≥ 110 then available else max 4 (available - graph.size - 1)
  let mut code := #[]
  if let some source := run.program.source then
    code := code.push s!"Source: {source.file} (bundled with deployed image)"
    let sourceLines := source.text.splitOn "\n" |>.toArray
    let start := min (sourceLines.size - 1) ((if sourceOffset == 0 then sourceStart run events else sourceOffset) - 1)
    for index in [start:min sourceLines.size (start + codeRows - 1)] do
      let markers := events.foldl (fun text (worker, trace) =>
        match lastEvent trace with
        | none => text
        | some e =>
          let alive := nodes.any (fun n => n.name == ctx.container run worker && n.state == "running")
          if alive && e.activity != "returned" && (source.sites.any fun site => site.operation == e.operation && site.line == index + 1) then
            text ++ (worker.drop 6 |>.toString)
          else text) ""
      code := code.push s!"{pad 3 (toString (index + 1))} {pad 3 markers} {sourceLines[index]!}"
  else code := #["This program has no bundled source locations."]
  if width ≥ 110 then
    let left := width / 2
    for i in [:max code.size graph.size] do
      lines := lines.push (pad left (code[i]?.getD "") ++ " │ " ++ (graph[i]?.getD ""))
  else lines := lines ++ code ++ #[""] ++ graph
  lines := lines.push "CPU is per container; I/O graphs are rates; · means no rate sample."
  return (lines.extract 0 (height - 1)).map (clip width)

private structure Navigation where
  selected : Nat := 0
  offset : Nat := 0

/-- Redraw from the cached snapshot while reading keys; return for a refresh or quit. -/
private partial def watchKeys (draw : Navigation → Cli Unit) (autoOffset refresh : Nat)
    (nav : Navigation) (redraw := true) : Cli (Option Navigation) := do
  if redraw then draw nav
  let key ← request (.key 100)
  if key == 113 || key == 3 || key == 4 || key == 27 then return none
  let offset := if nav.offset == 0 then autoOffset else nav.offset
  let nav := match key.toNat with
    | 9 => { nav with selected := nav.selected + 1 }
    | 49 | 50 | 51 => { nav with selected := key.toNat - 49 }
    | 106 => { nav with offset := offset + 3 }
    | 107 => { nav with offset := max 1 (offset - 3) }
    | 97 => { nav with offset := 0 }
    | _ => nav
  if key == 0 && (← request .now) ≥ refresh then return some nav
  watchKeys draw autoOffset refresh nav (key != 0)

private partial def watchLoop (ctx : Context) (run : Run) (interactive : Bool)
    (history : Array History := #[]) (nav : Navigation := {}) : Cli Unit := do
  let nodes := runNodes run (← ctx.nodes)
  let events ← ctx.events run nodes
  let history := remember history (← samples nodes)
  let control ← ctx.control run.id
  let status ← try
    pure ((← ctx.outcome run).map exitLabel |>.getD
      (if control != .active then control.label else "result pending"))
    catch _ => pure (if control != .active then control.label else "result unavailable")
  let diskNode := nav.selected % max 1 nodes.size
  let disk ← match nodes[diskNode]? with
    | some node => filesystem node
    | none => pure none
  let (width, height) ← if interactive then request .dimensions else pure (120, 35)
  let draw (nav : Navigation) : Cli Unit := do
    let disk := if nav.selected % max 1 nodes.size == diskNode then disk else none
    let lines := frame ctx run nodes events history nav.selected nav.offset width height status disk
    if interactive then request (.write "\x1b[H\x1b[2J")
    printLine (String.intercalate "\n" lines.toList)
    request .flush
  if !interactive then draw nav; return
  let refresh := (← request .now) + 1000
  let some nav ← watchKeys draw (sourceStart run events) refresh nav | return
  watchLoop ctx run interactive history nav

private def watch (ctx : Context) (id : String) (once := false) : Cli Unit := do
  let run ← ctx.loadRun id
  let interactive ← if once then pure false else request .enterTerminal
  try
    if interactive then request (.write "\x1b[?1049h\x1b[?25l")
    watchLoop ctx run interactive
  finally
    if interactive then
      request .leaveTerminal
      request (.write "\x1b[?25h\x1b[?1049l")
      request .flush

private def help : String := "Commands:\n  init DIRECTORY               Create and select a cloud application\n  open DIRECTORY               Select an existing application\n  deploy [EXECUTABLE]           Build this application's image and start shared services\n  deployments                  List known deployments, including stopped ones\n  use NAME                     Select and remember a deployment\n  status                       Show selected deployment health\n  up                           Start services without rebuilding\n  doctor                       Diagnose local configuration and Docker\n  down                         Stop this deployment, preserving its data\n  programs                     List compiled entry points\n  run PROGRAM [--input FILE] [--id ID]\n  ps                           List runs launched from this checkout\n  inspect RUN                  Inspect scheduler jobs and assignments\n  result RUN                   Read the durable result\n  watch RUN [--once]            Live source positions and container graphs\n  nodes                        Inspect workers, schedulers, brokers and blobs\n  logs RUN [worker1|worker2|worker3|scheduler]\n  pause RUN                    Stop a run and preserve replay state\n  kill RUN                     Permanently cancel a run\n  resume RUN                   Resume a paused run or repair a launch\n  help | quit"

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
  match args with
  | [] => return true
  | ["quit"] | ["exit"] => return false
  | ["help"] | ["--help"] => printLine help
  | ["deploy"] => ctx.deploy
  | ["deploy", executable] => ctx.deploy (some executable)
  | ["down"] => ctx.down
  | ["up"] => ctx.up
  | ["deployments"] => listDeployments ctx
  | ["status"] => ctx.status
  | ["doctor"] => ctx.doctor
  | ["init", directory] => Project.init ctx directory
  | ["init", directory, "--sdk", path] => Project.init ctx directory (some path)
  | ["programs"] =>
    for program in (← ctx.deployment).programs do
      printLine s!"{pad 25 program.entry}{safe program.description}"
  | "run" :: name :: args =>
    let (file, id) ← liftExcept (runOptions args)
    ctx.launch name file id
  | ["ps"] => listRuns ctx
  | ["inspect", id] => inspectRun ctx id
  | ["nodes"] => showNodes ctx
  | ["resume", id] => ctx.resume id
  | ["pause", id] => ctx.pause id
  | ["kill", id] => ctx.kill id
  | ["watch", id] => watch ctx id
  | ["watch", id, "--once"] => watch ctx id true
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
    unless ["worker1", "worker2", "worker3", "scheduler"].contains role do throw "Unknown actor"
    let run ← ctx.loadRun id
    let output ← docker #["logs", "--tail", "100", ctx.container run role]
    for line in (output.stdout ++ output.stderr).splitOn "\n" do printLine (safe line)
  | _ => throw "Unknown command. Use 'help'."
  return true

/-- Project selection belongs to the CLI state, not the process's working directory. -/
def dispatch (ctx : Context) (args : List String) : Cli (Context × Bool) := do
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
