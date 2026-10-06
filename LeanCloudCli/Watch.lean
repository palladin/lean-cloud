import LeanCloudCli.SnapshotMetrics
import LeanCloudCli.Input
import LeanCloudCli.BranchTree

namespace LeanCloudCli.Watch
open Lean LeanCloud

structure Navigation where
  offset : Nat := 0
  workers : Nat := 0
  tree : BranchTree.Navigation := {}
  deriving BEq, Inhabited

def navigate (steps : Array Trace.Step) (autoOffset : Nat)
    (nav : Navigation) (key : Input.Key) (lastPage : Nat := 0) : Navigation :=
  if [.left, .right, .up, .down, .enter].contains key then
    let tree := BranchTree.navigate (BranchTree.current steps) nav.tree key
    { nav with tree, offset := 0, workers := 0 }
  else
    let offset := if nav.offset == 0 then autoOffset else nav.offset
    match key with
    | .pageUp => { nav with workers := nav.workers - 1 }
    | .pageDown => { nav with workers := min lastPage (nav.workers + 1) }
    | .home => { nav with workers := 0 }
    | .text "j" => { nav with offset := offset + 3 }
    | .text "k" => { nav with offset := max 1 (offset - 3) }
    | .text "a" => { nav with offset := 0 }
    | _ => nav

def sourcePosition (run : Run) (step : Trace.Step) : Option (ProgramSource × SourceSite) := do
  let id ← step.event.source
  run.program.sources.findSome? fun source =>
    (source.sites.find? (·.id == id)).map (source, ·)

private def assignment (entry : BranchTree.Entry) : Option (String × Nat) := do
  unless entry.control.isEmpty do none
  let job ← entry.job
  match job.status with
  | .running worker attempt => some (worker, attempt)
  | _ => none

private def branchCode (steps : Array Trace.Step) (row : BranchTree.Row) : Array Trace.Step :=
  let own := BranchTree.observations steps row.branch
  let fork := row.fork.orElse fun _ =>
    if own.isEmpty && row.branch.size > 1 then some (row.branch.extract 0 (row.branch.size - 1)) else none
  match fork with
  | none => own
  | some fork => steps.filter fun s => s.event.worker != "scheduler" &&
      s.event.location == fork.key && s.event.source.isSome

private def mapped (run : Run) (steps : Array Trace.Step) : Option (ProgramSource × SourceSite) :=
  steps.findSomeRev? (sourcePosition run)

private def sourceStart (run : Run) (steps : Array Trace.Step) (nav : Navigation) : Nat :=
  let line := do
    let row ← BranchTree.selected (BranchTree.current steps) nav.tree
    let (_, site) ← mapped run (branchCode steps row)
    pure site.line
  max 1 (line.getD 1 - 1)

/-- Running views sample Docker; stopped views use the frozen meter window. -/
def metrics (ctx : Context) (worker : String) (steps : Array Trace.Step)
    (histories : Array History) (disks : Array (String × DiskUsage)) (live : Bool)
    (width : Nat) : Array Styled.Line :=
  if live then
    let history := histories.find? (fun h => h.name == ctx.node worker && h.fresh)
    let disk := (disks.find? (·.1 == ctx.node worker)).map (·.2)
    metricLines (history.map (·.points) |>.getD #[]) width disk
  else SnapshotMetrics.lines (SnapshotMetrics.samples steps worker) width

private def sourceRows (run : Run) (steps : Array Trace.Step)
    (rows offset : Nat) : Array Styled.Line := Id.run do
  let position := mapped run steps
  let some source := position.map (·.1) |>.orElse (fun _ => run.program.sources[0]?)
    | return #[Styled.text "Source not bundled" .muted]
  let line := position.map (·.2.line)
  let fallback := (source.sites[0]?.map (·.line)).getD 1
  let sourceLines := source.text.splitOn "\n" |>.toArray
  let start := min (sourceLines.size - 1) ((if offset == 0 then
    max 1 (line.getD fallback - (if rows > 2 then 1 else 0)) else offset) - 1)
  let mut result := #[]
  for i in [start:min sourceLines.size (start + rows)] do
    let marked := line == some (i + 1)
    result := result.push (Styled.text s!"{pad 4 (toString (i + 1))}{if marked then ">" else " "} {sourceLines[i]!}"
      (if marked then .selected else .normal))
  return result

private def sourceLabel (run : Run) (steps : Array Trace.Step) : String :=
  (mapped run steps).map (fun (source, site) => s!"{source.file}:{site.line}") |>.getD "source unavailable"

private def beside (left right : Array Styled.Line) (leftWidth : Nat) : Array Styled.Line :=
  (Array.range (max left.size right.size)).map fun row =>
    let content := Styled.slice (left[row]?.getD #[]) 0 leftWidth
    content ++ Styled.text (String.ofList (List.replicate (leftWidth - Styled.length content) ' ')) ++
      Styled.text " │ " .muted ++ (right[row]?.getD #[])

/-- Use the scheduler's current assignment and attempt, not a worker that ran
this branch earlier. This also excludes observations from a revoked attempt. -/
def executing (steps : Array Trace.Step) (entries : Array BranchTree.Entry)
    (worker : String) : Array Trace.Step :=
  match entries.findSome? (fun entry => (assignment entry).bind fun (name, attempt) =>
      if name == worker then some (entry.branch, attempt) else none) with
  | none => #[]
  | some (branch, attempt) => (BranchTree.observations steps branch).filter fun step =>
      step.event.worker == worker && step.event.attempt == some attempt

private def workerCard (ctx : Context) (run : Run) (steps : Array Trace.Step)
    (entries : Array BranchTree.Entry) (worker : String) (histories : Array History)
    (disks : Array (String × DiskUsage)) (live : Bool) (width height : Nat) : Array Styled.Line := Id.run do
  let current := entries.find? (fun entry => (assignment entry).map (·.1) == some worker)
  let code := if live then executing steps entries worker else steps.filter (·.event.worker == worker)
  let label := if live then current.map (fun entry => s!"branch {entry.branch.key}") |>.getD "idle for this workflow"
    else "last view"
  let mut lines := #[Styled.text (pad width s!" {worker} · {label}") .selected]
  if !live || current.isSome then
    lines := lines.push (Styled.text (sourceLabel run code) .muted)
    lines := lines ++ sourceRows run code (if height ≥ 10 then 2 else 1) 0
  else lines := lines.push (Styled.text "No branch executing" .muted)
  return (lines ++ metrics ctx worker steps histories disks live width).extract 0 height

private def workerCount (ctx : Context) (run : Run) (steps : Array Trace.Step) (histories : Array History) : Nat :=
  histories.foldl (fun count h =>
    max count ((workerIndex? (h.name.drop (ctx.project.length + 1) |>.toString)).map (· + 1) |>.getD 0))
      (steps.foldl (fun count s => max count ((workerIndex? s.event.worker).map (· + 1) |>.getD 0)) run.workers)

private def workerColumns (count width : Nat) := min count (max 1 (min 3 (width / 44)))

private def workerCapacity (count width height : Nat) :=
  max 1 (workerColumns count width * max 1 ((height - 1) / max 1 (min 12 (height - 1))))

private def workerGrid (ctx : Context) (run : Run) (steps : Array Trace.Step)
    (entries : Array BranchTree.Entry) (histories : Array History) (disks : Array (String × DiskUsage))
    (live : Bool) (page width height : Nat) : Array Styled.Line := Id.run do
  let count := workerCount ctx run steps histories
  if count == 0 then return #[Styled.text "No workers" .muted]
  let columns := workerColumns count width
  let cellWidth := (width - (columns - 1) * 3) / columns
  let cellHeight := min 12 (height - 1)
  let perPage := workerCapacity count width height
  let pages := max 1 ((count + perPage - 1) / perPage)
  let page := min page (pages - 1)
  let workers := (workerNames count).extract (page * perPage) ((page + 1) * perPage)
  let cards := workers.map fun worker => workerCard ctx run steps entries worker histories disks live cellWidth cellHeight
  let mut lines := #[Styled.text s!"Workers · {count} total · {page + 1}/{pages} · PgUp/PgDn" .cyan]
  for row in [:((cards.size + columns - 1) / columns)] do
    let mut combined := cards[row * columns]?.getD #[]
    for column in [1:columns] do
      combined := beside combined (cards[row * columns + column]?.getD #[]) (column * (cellWidth + 3) - 3)
    lines := lines ++ combined
  return lines.extract 0 height

private def branchPanel (ctx : Context) (run : Run) (steps : Array Trace.Step)
    (entries : Array BranchTree.Entry) (row : BranchTree.Row)
    (histories : Array History) (disks : Array (String × DiskUsage))
    (live : Bool) (width height : Nat) (nav : Navigation) : Array Styled.Line := Id.run do
  let own := BranchTree.observations steps row.branch
  let assigned := (entries.find? (·.branch == row.branch)) >>= assignment
  let worker := if live then assigned.map (·.1) else own.back?.map (·.event.worker)
  let code := if live && assigned.isSome && row.fork.isNone then
    executing steps entries (assigned.get!.1) else branchCode steps row
  let title := row.fork.map (fun fork => s!" Parallel {fork.key}") |>.getD s!" Branch {row.branch.key}"
  let codeRows := if row.fork.isSome then min 5 (max 2 (height / 5)) else min 12 (max 2 (height - 14))
  let mut lines := #[Styled.text (pad width title) .header,
    Styled.text row.status .cyan, Styled.text s!"Source: {sourceLabel run code}" .muted]
  lines := lines ++ sourceRows run code codeRows nav.offset
  if row.fork.isSome then
    lines := lines ++ workerGrid ctx run steps entries histories disks live nav.workers width (height - lines.size)
  else if let some worker := worker then
    lines := lines ++ #[Styled.text s!"{worker} · {if live then "executing" else "last view"}" .cyan] ++
      metrics ctx worker (if live then steps else own) histories disks live width
  else lines := lines.push (Styled.text "No worker executing this branch" .muted)
  return lines.extract 0 height

/-- Live tree and code. Completion freezes the last view; no event list or cursor. -/
def frame (ctx : Context) (run : Run) (steps : Array Trace.Step)
    (histories : Array History) (nav : Navigation) (width height : Nat)
    (status := "") (disks : Array (String × DiskUsage) := #[]) (color := false) (warning := "")
    (timing : Option Timing.Run := none)
    : Array String := Id.run do
  let width := width - 1
  let entries := BranchTree.current steps
  let live := status == "result pending"
  let mut lines := #[
    Styled.text (pad width s!" {run.id} · {status} · {run.program.entry} / {ctx.project}") .header,
    Styled.text "↑↓: branch · ←→: fold · PgUp/PgDn: workers · j/k: code · a: follow source · q: back" .cyan,
    Styled.text (if live then "LIVE" else "LAST VIEW") .muted]
  if width < 39 || height < 16 then
    lines := lines.push (Styled.text "Enlarge terminal to at least 40 × 16." .yellow)
  else
    let sidebar := width ≥ 100
    let treeWidth := if sidebar then min 52 (max 38 (width / 4)) else width
    let bodyWidth := if sidebar then width - treeWidth - 3 else width
    let bodyHeight := height - 5 - (if sidebar then 0 else 5)
    let body := match BranchTree.selected entries nav.tree with
      | some row => branchPanel ctx run steps entries row histories disks live bodyWidth bodyHeight nav
      | none => #[Styled.text "Source: waiting for branch observations" .muted]
    let tree := BranchTree.lines entries nav.tree (if sidebar then height - 5 else 5) treeWidth timing
    lines := lines ++ (if sidebar then beside tree body treeWidth else tree ++ body)
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
  if !outcome.isOk && (← request (.exists path)) then
    return (← readJson (α := String) path) ++ " (saved)"
  if control != .active then return control.label
  if outcome.isOk then return "result pending"
  return "result unavailable"

private def terminal (status : String) : Bool :=
  ["completed", "failed", "cancelled", "killed"].any (fun label => status.startsWith label)

private partial def wait (draw : Navigation → Nat → Nat → Cli Unit) (lastPage : Nat → Nat → Nat)
    (run : Run) (steps : Array Trace.Step) (refresh : Option Nat) (nav : Navigation)
    (size : Nat × Nat) : Cli (Option Navigation) := do
  let key ← Input.read
  if [.text "q", .escape, .interrupt, .eof].contains key then return none
  let nextSize ← request .dimensions
  let next := navigate steps (sourceStart run steps nav) nav key (lastPage nextSize.1 nextSize.2)
  let next := { next with workers := min next.workers (lastPage nextSize.1 nextSize.2) }
  if next != nav || nextSize != size then draw next nextSize.1 nextSize.2
  if refresh.any ((← request .now) ≥ ·) then return some next
  wait draw lastPage run steps refresh next nextSize

private partial def loop (ctx : Context) (run : Run) (interactive color : Bool)
    (history : Array History := #[]) (nav : Navigation := {}) : Cli Unit := do
  let snapshot ← Trace.load ctx run
  let status ← status ctx run
  let (timing, timingAvailable) ← ctx.timingSnapshot run
  let live := status == "result pending"
  let nodes ← if live then try ctx.nodes catch _ => pure #[] else pure #[]
  let nodes := nodes.filter (fun node => (workerIndex? node.role).isSome)
  let values ← if live then try samples nodes catch _ => pure #[] else pure #[]
  let history := if live then remember history values else history
  let mut disks := #[]
  for node in nodes do
    let disk ← try filesystem node catch _ => pure none
    if let some disk := disk then disks := disks.push (node.name, disk)
  let (width, height) ← if interactive then request .dimensions else pure (120, 35)
  let draw (nav : Navigation) (width height : Nat) : Cli Unit := do
    let lines := frame ctx run snapshot.steps history nav width height status disks color snapshot.warning timing
    if interactive then request (.write "\x1b[H\x1b[2J")
    request (.write (String.intercalate "\n" lines.toList ++ "\n"))
    request .flush
  draw nav width height
  if !interactive then return
  let now ← request .now
  let awaitingTiming := timingAvailable && timing.any (fun timing => timing.span.any (·.finishedMs.isNone))
  let refresh := if terminal status && !awaitingTiming then none else some (now + 1000)
  let lastPage (width height : Nat) :=
    let width := width - 1
    let sidebar := width ≥ 100
    let bodyWidth := if sidebar then width - min 52 (max 38 (width / 4)) - 3 else width
    let bodyHeight := height - 5 - (if sidebar then 0 else 5)
    let count := workerCount ctx run snapshot.steps history
    let capacity := workerCapacity count bodyWidth (bodyHeight - 3 - min 5 (max 2 (bodyHeight / 5)))
    (count + capacity - 1) / capacity - 1
  let some nav ← wait draw lastPage run snapshot.steps refresh nav (width, height) | return
  loop ctx run interactive color history nav

/-- Watching is an Eff program and never submits or resumes a workflow. -/
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
