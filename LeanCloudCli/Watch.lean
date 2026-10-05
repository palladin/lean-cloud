import LeanCloudCli.RecordedMetrics
import LeanCloudCli.Input

namespace LeanCloudCli.Watch
open Lean LeanCloud

structure Navigation where
  selected : Nat := 0
  offset : Nat := 0
  worker : Option String := none
  /-- Stable event identity, so refreshes do not move a historical selection. -/
  cursor : Option String := none
  workerPage : Nat := 0
  deriving BEq, Inhabited

def index (steps : Array Trace.Step) (nav : Navigation) : Nat :=
  (nav.cursor >>= fun id => steps.findIdx? (·.id == id)).getD (steps.size - 1)

def visible (steps : Array Trace.Step) (nav : Navigation) : Array Trace.Step :=
  match nav.worker with
  | none => steps
  | some worker => steps.filter (·.event.worker == worker)

def navigate (steps : Array Trace.Step) (autoOffset page : Nat)
    (nav : Navigation) (key : Input.Key) (workers := defaultWorkerCount) : Navigation := Id.run do
  let allSteps := steps
  let steps := visible steps nav
  let current := index steps nav
  let select (i : Nat) := { nav with cursor := (steps[min i (steps.size - 1)]?).map (·.id), offset := 0 }
  let focus (i : Nat) := Id.run do
    let worker := s!"worker{i + 1}"
    let cutoff := (nav.cursor >>= fun id => allSteps.findIdx? (·.id == id)).getD (allSteps.size - 1)
    let prior := (allSteps.extract 0 (cutoff + 1)).findSomeRev? fun step =>
      if step.event.worker == worker then some step.id else none
    let cursor := if nav.cursor.isNone then none else
      prior.orElse (fun _ => (allSteps.find? (·.event.worker == worker)).map (·.id))
    return { nav with worker := some worker, selected := i, cursor, offset := 0, workerPage := i / 3 }
  let offset := if nav.offset == 0 then autoOffset else nav.offset
  return match key with
    | .left | .up => select (current - 1)
    | .right | .down => select (current + 1)
    | .pageUp => select (current - page)
    | .pageDown => select (current + page)
    | .home => select 0
    | .end | .text "f" => { nav with cursor := none, offset := 0 }
    | .text "g" | .text "0" => { nav with worker := none, offset := 0 }
    | .tab => if workers == 0 then nav else if nav.worker.isNone then focus 0 else
        if nav.selected + 1 ≥ workers then { nav with worker := none, offset := 0 } else focus (nav.selected + 1)
    | .backTab => if workers == 0 then nav else if nav.worker.isNone then focus (workers - 1) else
        if nav.selected == 0 then { nav with worker := none, offset := 0 } else focus (nav.selected - 1)
    | .text "[" => { nav with workerPage := nav.workerPage - 1 }
    | .text "]" => { nav with workerPage := min ((workers - 1) / 3) (nav.workerPage + 1) }
    | .text "1" => if nav.workerPage * 3 < workers then focus (nav.workerPage * 3) else nav
    | .text "2" => if nav.workerPage * 3 + 1 < workers then focus (nav.workerPage * 3 + 1) else nav
    | .text "3" => if nav.workerPage * 3 + 2 < workers then focus (nav.workerPage * 3 + 2) else nav
    | .text "j" => { nav with offset := offset + 3 }
    | .text "k" => { nav with offset := max 1 (offset - 3) }
    | .text "a" => { nav with offset := 0 }
    | _ => nav

def sourcePosition (run : Run) (step : Trace.Step) : Option (ProgramSource × SourceSite) := do
  let id ← step.event.source
  run.program.sources.findSome? fun source =>
    (source.sites.find? (·.id == id)).map (source, ·)

def sourceLine (run : Run) (step : Trace.Step) : Option Nat :=
  (sourcePosition run step).map (·.2.line)

private def sourceStart (run : Run) (steps : Array Trace.Step) (nav : Navigation) (context := 1) : Nat :=
  let displayed := visible steps nav
  let selected := displayed[index displayed nav]?
  let mapped := selected >>= sourceLine run
  let previous := selected >>= fun selected => do
    let cutoff ← steps.findIdx? (·.id == selected.id)
    (steps.extract 0 (cutoff + 1)).findSomeRev? fun step =>
      if step.event.worker == selected.event.worker then sourceLine run step else none
  let fallback := (run.program.sources[0]? >>= fun source => source.sites[0]?.map (·.line)).getD 1
  max 1 ((mapped.orElse (fun _ => previous)).getD fallback - context)

private def tableRows (height : Nat) := max 1 (min 7 ((height - 16) / 2))

private def workerStep (steps : Array Trace.Step) (worker : String) : Option Trace.Step :=
  steps.findSomeRev? fun step => if step.event.worker == worker then some step else none

private def workerSource (run : Run) (observed : Array Trace.Step) (worker : String) : Option Trace.Step := do
  let latest ← workerStep observed worker
  if (sourceLine run latest).isSome then return latest
  observed.findSomeRev? fun step =>
    if step.event.worker == worker && step.event.session == latest.event.session &&
        step.event.attempt == latest.event.attempt && step.event.location == latest.event.location &&
        (sourceLine run step).isSome then some step else none

/-- Historical metrics use only the trace prefix ending at the cursor. -/
def metrics (ctx : Context) (worker : String) (observed : Array Trace.Step)
    (histories : Array History) (disks : Array (String × DiskUsage)) (live : Bool)
    (width : Nat) (compact := false) : Array Styled.Line :=
  if live then
    let history := histories.find? (fun h => h.name == ctx.node worker && h.fresh)
    let points := history.map (·.points) |>.getD #[]
    let disk := (disks.find? (·.1 == ctx.node worker)).map (·.2)
    if compact then
      match points.back? with
      | none => #[Styled.text "Live stats unavailable" .muted]
      | some p => #[Styled.text s!"CPU {percent p.cpu} · Mem {humanBytes p.memory}" .green]
    else metricLines points width disk
  else RecordedMetrics.lines (RecordedMetrics.history observed worker) width compact

private def sourceRows (run : Run) (observed : Array Trace.Step) (worker : String)
    (rows offset : Nat) : Array Styled.Line := Id.run do
  let mapped := workerSource run observed worker
  let some source := (mapped >>= sourcePosition run).map (·.1) |>.orElse (fun _ => run.program.sources[0]?)
    | return #[Styled.text "Source not bundled" .muted]
  let line := mapped >>= sourceLine run
  let latest := workerStep observed worker
  let exact := mapped.map (·.id) == latest.map (·.id) && mapped.isSome
  let fallback := (source.sites[0]?.map (·.line)).getD 1
  let sourceLines := source.text.splitOn "\n" |>.toArray
  let start := min (sourceLines.size - 1) ((if offset == 0 then
    max 1 (line.getD fallback - (if rows > 2 then 1 else 0)) else offset) - 1)
  let mut result := #[]
  for i in [start:min sourceLines.size (start + rows)] do
    let marked := line == some (i + 1)
    let arrow := if marked then (if exact then ">" else "~") else " "
    result := result.push (Styled.text s!"{pad 4 (toString (i + 1))}{arrow} {sourceLines[i]!}"
      (if marked then .selected else .normal))
  return result

private def tabBar (nav : Navigation) (compact : Bool) (workers : Nat) : Styled.Line :=
  let start := min nav.workerPage ((workers - 1) / 3) * 3
  (#[ (none, "g Global") ] ++ (Array.range (min 3 (workers - start))).map (fun i =>
    (some s!"worker{start + i + 1}", if compact then s!"{i + 1} W{start + i + 1}" else s!"{i + 1} Worker {start + i + 1}"))).foldl
    (fun line (worker, label) => line ++ Styled.text ("[" ++ label ++ "]")
      (if nav.worker == worker then .selected else .cyan) ++ Styled.text " ") #[]

private def timestamp (value : String) : String :=
  (value.take 23 |>.toString) ++ (if value.endsWith "Z" then "Z" else "")

private def panel (ctx : Context) (run : Run) (observed : Array Trace.Step)
    (histories : Array History) (disks : Array (String × DiskUsage)) (worker : String)
    (live compact : Bool) (width codeRows offset : Nat) : Array Styled.Line := Id.run do
  let step := workerStep observed worker
  let detail := match step with
    | none => "No observed work yet"
    | some s => s!"{s.event.location} · {s.event.activity} {s.event.operation}"
  let stamp := if live then "LIVE stats" else
    match observed.findSomeRev? (fun s => if s.event.worker == worker && s.resources.isSome then some s else none) with
    | none => "Recorded metrics"
    | some s => "Recorded " ++ timestamp s.timestamp
  let title := Styled.text (pad width s!" {worker} · {if live then "Live" else "History"}") .header
  let position := workerSource run observed worker >>= sourcePosition run
  let file := position.map (fun (source, site) => s!"{source.file}:{site.line}") |>.getD "source unavailable"
  let code := sourceRows run observed worker codeRows offset
  if compact then
    return #[Styled.text (pad width s!" {worker} · {file} · {detail}") .header] ++ code ++
      metrics ctx worker observed histories disks live width true
  return #[title, Styled.text detail .cyan,
      Styled.text s!"Source: {file}" .muted] ++ code ++
    #[Styled.text stamp .muted] ++ metrics ctx worker observed histories disks live width

/-- Global pages cover every worker. Each panel has its own code window and
stats at the selected moment. Local expands one panel and its ordered steps. -/
def frame (ctx : Context) (run : Run) (nodes : Array Node) (steps : Array Trace.Step)
    (histories : Array History) (nav : Navigation) (width height : Nat)
    (status := "") (disks : Array (String × DiskUsage) := #[]) (color := false) (warning := "")
    : Array String := Id.run do
  let width := width - 1
  let workers := steps.foldl (fun count step =>
    max count ((workerIndex? step.event.worker).map (· + 1) |>.getD 0)) run.workers
  let workers := nodes.foldl (fun count node =>
    max count ((workerIndex? node.role).map (· + 1) |>.getD 0)) workers
  let displayed := visible steps nav
  let position := index displayed nav
  let selected := displayed[position]?
  let globalPosition := (selected >>= fun s => steps.findIdx? (·.id == s.id)).getD (steps.size - 1)
  let observed := steps.extract 0 (globalPosition + 1)
  let live := nav.cursor.isNone && status == "result pending"
  let mode := if live then "FOLLOWING LIVE" else "HISTORY · recorded stats"
  let scope := nav.worker.getD "GLOBAL"
  let moment := selected.map (fun s => timestamp s.timestamp) |>.getD ""
  let mut lines := #[
    Styled.text (pad width s!" {run.id} · {status} · {run.program.entry} / {ctx.project}") .header,
    tabBar nav (width < 60) workers,
    Styled.text s!"Tab: view · [/]: workers {min nav.workerPage ((workers - 1) / 3) + 1}/{max 1 ((workers + 2) / 3)} · arrows: step · Home/End · q: back" .cyan,
    Styled.text s!"{scope} · {mode} · Step {if displayed.isEmpty then 0 else position + 1}/{displayed.size} · {moment}" .cyan]
  if width < 39 || height < 16 then
    lines := lines.push (Styled.text "Enlarge terminal to at least 40 × 16." .yellow)
  else
    let selectedText := match selected with
      | none => "No retained steps in this view."
      | some s => s!"> {s.event.worker} {s.event.location} · {s.event.activity} {s.event.operation}"
    -- Three cards per page keep code legible; Tab reaches every worker.
    let start := min nav.workerPage ((workers - 1) / 3) * 3
    let workers := nav.worker.map (fun w => #[w]) |>.getD ((workerNames workers).extract start (start + 3))
    let panels := max 1 workers.size
    let columns := if nav.worker.isNone && width ≥ 110 then panels else 1
    let compact := nav.worker.isNone && (height - 8) / (panels / columns) < 13
    let codeRows := if compact then 1
      else if nav.worker.isSome then max 2 (height - 21) else max 2 (min 7 (height - 21))
    let cellWidth := (width - (columns - 1) * 3) / columns
    let cards := workers.map fun worker =>
      panel ctx run observed histories disks worker live compact cellWidth codeRows
        (if nav.worker.isSome then nav.offset else 0)
    if workers.isEmpty then lines := lines.push (Styled.text "No worker capacity. Use 'scale N' to add workers." .yellow)
    if columns > 1 then
      for row in [:cards.foldl (fun n c => max n c.size) 0] do
        let mut joined := #[]
        for col in [:columns] do
          if col > 0 then joined := joined ++ Styled.text " │ " .muted
          let content := Styled.slice ((cards[col]?.getD #[])[row]?.getD #[]) 0 cellWidth
          joined := joined ++ content ++ Styled.text (String.ofList (List.replicate (cellWidth - Styled.length content) ' '))
        lines := lines.push joined
    else
      for card in cards do lines := lines ++ card
    lines := lines.push (Styled.text selectedText .selected)
    let available := height - lines.size - 3
    let count := min 5 available
    let start := min (position - count / 2) (displayed.size - count)
    for i in [start:min displayed.size (start + count)] do
      let e := displayed[i]!.event
      lines := lines.push (Styled.text s!"{if i == position then ">" else " "}{i + 1}  {e.worker}  {e.location}  {e.activity} {e.operation}"
        (if i == position then .selected else .normal))
    lines := lines.push (Styled.text (if compact then "Compact overview · 1/2/3: full code and stats"
      else "> mapped step; ~ last mapped line · PgUp/PgDn: steps · j/k: code") .muted)
    if !warning.isEmpty then lines := lines.push (Styled.text warning .yellow)
  return (lines.extract 0 (height - 1)).map (fun line => Styled.render line width color)

private def exitLabel : Exit → String
  | .success _ => "completed"
  | .failure error => s!"failed: {safe error.message}"
  | .cancelled _ => "cancelled"

private def status (ctx : Context) (run : Run) : Cli String := do
  let control ← ctx.control run.id
  let path := ctx.directory run.id / "watch-status.json"
  let outcome ← observing (ctx.outcome run)
  if let .ok (some outcome) := outcome then
    let label := exitLabel outcome
    saveJson path label
    return label
  -- Root outcomes are immutable. A later local pause/kill intent cannot replace
  -- a confirmed terminal result when the deployment is temporarily offline.
  if !outcome.isOk && (← request (.exists path)) then
    return (← readJson (α := String) path) ++ " (saved)"
  if control != .active then return control.label
  if outcome.isOk then return "result pending"
  return "result unavailable"

private partial def wait (draw : Navigation → Nat → Nat → Cli Unit)
    (run : Run) (steps : Array Trace.Step) (refresh : Nat) (nav : Navigation)
    (size : Nat × Nat) : Cli (Option Navigation) := do
  let key ← Input.read
  if [.text "q", .escape, .interrupt, .eof].contains key then return none
  let nextSize ← request .dimensions
  let next := navigate steps (sourceStart run steps nav) (tableRows nextSize.2) nav key run.workers
  if next != nav || nextSize != size then draw next nextSize.1 nextSize.2
  if (← request .now) ≥ refresh then return some next
  wait draw run steps refresh next nextSize

private partial def loop (ctx : Context) (run : Run) (interactive color : Bool)
    (history : Array History := #[]) (nav : Navigation := {}) : Cli Unit := do
  let snapshot ← Trace.load ctx run
  let status ← status ctx run
  let count ← if status == "result pending" then
    try pure (← ctx.deployment).workers catch _ => pure 0
    else pure 0
  let count := snapshot.steps.foldl (fun count step =>
    max count ((workerIndex? step.event.worker).map (· + 1) |>.getD 0)) (max run.workers count)
  let run := { run with workers := count }
  let live := nav.cursor.isNone && status == "result pending"
  let nodes ← if live then try pure (runNodes run (← ctx.nodes)) catch _ => pure #[] else pure #[]
  let nodes := nodes.filter (fun node => (workerIndex? node.role).isSome)
  let values ← if live then try samples nodes catch _ => pure #[] else pure #[]
  let history := remember history values
  let mut disks := #[]
  for node in nodes do
    let disk ← try filesystem node catch _ => pure none
    if let some disk := disk then disks := disks.push (node.name, disk)
  let (width, height) ← if interactive then request .dimensions else pure (120, 35)
  let draw (nav : Navigation) (width height : Nat) : Cli Unit := do
    let lines := frame ctx run nodes snapshot.steps history nav width height status disks color snapshot.warning
    if interactive then request (.write "\x1b[H\x1b[2J")
    request (.write (String.intercalate "\n" lines.toList ++ "\n"))
    request .flush
  draw nav width height
  if !interactive then return
  let some nav ← wait draw run snapshot.steps ((← request .now) + 1000) nav (width, height) | return
  loop ctx run interactive color history nav

/-- Browsing is an Eff program and never submits or resumes a workflow. -/
def run (ctx : Context) (id : String) (once := false) : Cli Unit := do
  let run ← ctx.loadRun id
  let interactive ← if once then pure false else request .enterTerminal
  try
    if interactive then request (.write "\x1b[?1049h\x1b[?25l")
    loop ctx run interactive (interactive && (← colorsEnabled))
  finally
    if interactive then
      try request .leaveTerminal
      finally
        request (.write "\x1b[?25h\x1b[?1049l")
        request .flush

end LeanCloudCli.Watch
