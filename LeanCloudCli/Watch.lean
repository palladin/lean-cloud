import LeanCloudCli.SnapshotMetrics
import LeanCloudCli.Input
import LeanCloudCli.BranchTree
import LeanCloudCli.Fetch

namespace LeanCloudCli.Watch
open Lean LeanCloud

structure Navigation where
  offset : Nat := 0
  workers : Nat := 0
  tree : BranchTree.Navigation := {}
  deriving BEq, Inhabited

def navigate (steps : Array Trace.Step) (autoOffset : Nat)
    (nav : Navigation) (key : Input.Key) (lastPage : Nat := 0)
    (jobs : Array BranchObservation := #[]) : Navigation :=
  if [.left, .right, .up, .down, .enter].contains key then
    let tree := BranchTree.navigate (BranchTree.current steps jobs) nav.tree key
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

private def sourceStart (run : Run) (steps : Array Trace.Step) (nav : Navigation)
    (jobs : Array BranchObservation) : Nat :=
  let line := do
    let row ← BranchTree.selected (BranchTree.current steps jobs) nav.tree
    let (_, site) ← mapped run (branchCode steps row)
    pure site.line
  max 1 (line.getD 1 - 1)

/-- Running views use deployment counters; stopped views use the frozen window. -/
def metrics (ctx : Context) (worker : String) (steps : Array Trace.Step)
    (histories : Array History) (live : Bool)
    (width : Nat) : Array Styled.Line :=
  if live then
    let history := histories.find? (fun h => h.name == ctx.node worker && h.fresh)
    SnapshotMetrics.lines (history.map (·.resources) |>.getD #[]) width
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
  (mapped run steps).map (fun (source, site) =>
    let position := s!"{source.file}:{site.line}"
    site.functionInfo.map (fun info => s!"{safe info.descr} · {position}") |>.getD position)
    |>.getD "source unavailable"

/-- Progress belongs to the last executing command, not an earlier command or
worker incarnation. Keep it when completion freezes that command's last view.
Never sum worker counters: duplicate execution is not additional build progress. -/
private def progressUpdates (steps : Array Trace.Step) : Array (String × ProgressUpdate) := Id.run do
  let some current := steps.findSomeRev? (fun step =>
    if step.progress.isNone && (step.event.source.isSome || step.event.activity == "execute") then
      some step.event else none)
    | return #[]
  let mut seen : Std.HashSet String := {}
  let mut updates := #[]
  for step in steps.reverse do
    unless step.event.worker == current.worker && step.event.session == current.session &&
        step.event.attempt == current.attempt && step.event.location == current.location do continue
    if let some (slot, update) := step.progress then
      if seen.contains slot then continue
      seen := seen.insert slot
      updates := updates.push (slot, update)
  -- Numeric suffixes keep builder-2 before builder-10. Arrival order never
  -- changes a slot's row; a later report only replaces that slot's message.
  let key (slot : String) :=
    let digits := slot.toList.reverse.takeWhile Char.isDigit
    ((slot.dropEnd digits.length).toString, (String.ofList digits.reverse).toNat?.getD 0, slot)
  return updates.qsort fun a b =>
    if a.2.total.isSome != b.2.total.isSome then a.2.total.isSome
    else
      let (prefixA, numberA, nameA) := key a.1
      let (prefixB, numberB, nameB) := key b.1
      if prefixA != prefixB then prefixA < prefixB
      else if numberA != numberB then numberA < numberB
      else nameA < nameB

def progressLines (steps : Array Trace.Step) (limit : Nat := steps.size) : Array Styled.Line :=
  ((progressUpdates steps).extract 0 limit).map fun (slot, update) =>
    let count := match update.total with
      | some total => s!"{update.completed}/{total} · {if total == 0 then 100 else min 100 (update.completed * 100 / total)}% · "
      | none => ""
    Styled.text s!"{safe slot}: {count}{safe update.message}" .green

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

private def workerCode (steps : Array Trace.Step) (entries : Array BranchTree.Entry)
    (worker : String) (live : Bool) : Array Trace.Step :=
  if live then executing steps entries worker else steps.filter (·.event.worker == worker)

private def workerCard (ctx : Context) (run : Run) (steps : Array Trace.Step)
    (entries : Array BranchTree.Entry) (worker : String) (histories : Array History)
    (live : Bool) (width height : Nat) : Array Styled.Line := Id.run do
  let current := entries.find? (fun entry => (assignment entry).map (·.1) == some worker)
  let code := workerCode steps entries worker live
  let label := if live then current.map (fun entry => s!"branch {entry.branch.key}") |>.getD "idle for this workflow"
    else "last view"
  let mut lines := #[Styled.text (pad width s!" {worker} · {label}") .selected]
  if !live || current.isSome then
    lines := lines.push (Styled.text (sourceLabel run code) .muted)
    lines := lines ++ sourceRows run code (if height ≥ 10 then 2 else 1) 0
  else lines := lines.push (Styled.text "No branch executing" .muted)
  lines := lines ++ progressLines code
  return (lines ++ metrics ctx worker steps histories live width).extract 0 height

/-- Use reported node identities, including names chosen by external deployers. -/
def workerRoster (ctx : Context) (steps : Array Trace.Step) (histories : Array History) : Array String :=
  let names := histories.map (fun h => h.name.drop (ctx.project.length + 1) |>.toString) ++
    steps.map (·.event.worker)
  names.foldl (fun result name =>
    if name.isEmpty || name == "scheduler" || result.contains name then result else result.push name) #[]

private def workerColumns (count width : Nat) := min count (max 1 (min 3 (width / 44)))

private def workerCardHeight (steps : Array Trace.Step) (entries : Array BranchTree.Entry)
    (workers : Array String) (live : Bool) (height : Nat) : Nat :=
  let progress := workers.foldl (fun count worker =>
    max count (progressUpdates (workerCode steps entries worker live)).size) 0
  -- Header, source label, two code lines, progress, and nine metric lines.
  min (max 16 (13 + progress)) (height - 1)

private def workerCapacity (count width height cellHeight : Nat) :=
  max 1 (workerColumns count width * max 1 ((height - 1) / max 1 cellHeight))

private def groupCodeRows (height : Nat) := min 3 (max 2 (height / 5))

private def workerGrid (ctx : Context) (run : Run) (steps : Array Trace.Step)
    (entries : Array BranchTree.Entry) (histories : Array History)
    (live : Bool) (page width height : Nat) : Array Styled.Line := Id.run do
  let roster := workerRoster ctx steps histories
  let count := roster.size
  if count == 0 then return #[Styled.text "No workers" .muted]
  let columns := workerColumns count width
  let cellWidth := (width - (columns - 1) * 3) / columns
  let cellHeight := workerCardHeight steps entries roster live height
  let perPage := workerCapacity count width height cellHeight
  let pages := max 1 ((count + perPage - 1) / perPage)
  let page := min page (pages - 1)
  let workers := roster.extract (page * perPage) ((page + 1) * perPage)
  let cards := workers.map fun worker => workerCard ctx run steps entries worker histories live cellWidth cellHeight
  let mut lines := #[Styled.text s!"Workers · {count} total · {page + 1}/{pages} · PgUp/PgDn" .cyan]
  for row in [:((cards.size + columns - 1) / columns)] do
    let mut combined := cards[row * columns]?.getD #[]
    for column in [1:columns] do
      combined := beside combined (cards[row * columns + column]?.getD #[]) (column * (cellWidth + 3) - 3)
    lines := lines ++ combined
  return lines.extract 0 height

private def branchPanel (ctx : Context) (run : Run) (steps : Array Trace.Step)
    (entries : Array BranchTree.Entry) (row : BranchTree.Row)
    (histories : Array History)
    (live : Bool) (width height : Nat) (nav : Navigation) : Array Styled.Line := Id.run do
  let own := BranchTree.observations steps row.branch
  let assigned := (entries.find? (·.branch == row.branch)) >>= assignment
  let worker := if live then assigned.map (·.1) else own.back?.map (·.event.worker)
  let code := if live && assigned.isSome && row.fork.isNone then
    executing steps entries (assigned.get!.1) else branchCode steps row
  let title := if row.fork.isSome then s!" {row.title}" else s!" Branch {row.branch.key}"
  let progress := progressLines code
  let codeRows := if row.fork.isSome then groupCodeRows height
    else min 12 (max 2 (height - 13 - progress.size))
  let mut lines := #[Styled.text (pad width title) .header,
    Styled.text row.status .cyan, Styled.text s!"Source: {sourceLabel run code}" .muted]
  lines := lines ++ sourceRows run code codeRows nav.offset
  if row.fork.isSome then
    lines := lines ++ workerGrid ctx run steps entries histories live nav.workers width (height - lines.size)
  else if let some worker := worker then
    lines := lines ++ #[Styled.text s!"{worker} · {if live then "executing" else "last view"}" .cyan] ++
      progress ++
      metrics ctx worker (if live then steps else own) histories live width
  else lines := lines.push (Styled.text "No worker executing this branch" .muted)
  return lines.extract 0 height

/-- Live tree and code. Completion freezes the last view; no event list or cursor. -/
def frame (ctx : Context) (run : Run) (steps : Array Trace.Step)
    (histories : Array History) (nav : Navigation) (width height : Nat)
    (status := "") (color := false) (warning := "")
    (timing : Option Timing.Run := none)
    (jobs : Array BranchObservation := #[])
    : Array String := Id.run do
  let width := width - 1
  let control := if status.startsWith "paused" then some "paused"
    else if status.startsWith "killed" || status.startsWith "cancelled" then some "killed"
    else if status.startsWith "failed" then some "stopped"
    else if status == "result pending" then some "" else none
  -- Run status is authoritative even when diagnostic control events are missing
  -- or a paged refresh still contains an older pause event.
  let entries := (BranchTree.current steps jobs).map fun entry =>
    { entry with control := control.getD entry.control }
  let live := status == "result pending"
  let mut lines := #[
    Styled.text (pad width s!" {run.id} · {status} · {run.program.entry} / {ctx.project}") .header,
    Styled.text "↑↓: branch (wrap) · ←→: fold · PgUp/PgDn: workers · j/k: code · a: follow source · q: back" .cyan,
    Styled.text (if live then "LIVE" else "LAST VIEW") .muted]
  if width < 39 || height < 16 then
    lines := lines.push (Styled.text "Enlarge terminal to at least 40 × 16." .yellow)
  else
    let sidebar := width ≥ 100
    let treeWidth := if sidebar then min 52 (max 38 (width / 4)) else width
    let bodyWidth := if sidebar then width - treeWidth - 3 else width
    let bodyHeight := height - 5 - (if sidebar then 0 else 5)
    let body := match BranchTree.selected entries nav.tree with
      | some row => branchPanel ctx run steps entries row histories live bodyWidth bodyHeight nav
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
  let control ← observing (ctx.control run.id)
  let path := ctx.directory run.id / "watch-status.json"
  let outcome ← observing (ctx.outcome run)
  if let .ok (some outcome) := outcome then
    let label := exitLabel outcome
    saveJson path label
    return label
  if !outcome.isOk && (← request (.exists path)) then
    return (← readJson (α := String) path) ++ " (saved)"
  if let .ok control := control then
    if control != .active then
      saveJson path (controlLabel control)
      return (controlLabel control)
    if outcome.isOk then
      saveJson path "result pending"
      return "result pending"
  if ← request (.exists path) then
    return (← readJson (α := String) path) ++ " (saved)"
  return "result unavailable"

private def terminal (status : String) : Bool :=
  ["completed", "failed", "cancelled", "killed"].any (fun label => status.startsWith label)

private def moved (steps : Array Trace.Step) (run : Run) (nav : Navigation)
    (key : Input.Key) (lastPage : Nat) (jobs : Array BranchObservation := #[]) : Navigation :=
  if key == .idle then nav else
    navigate steps (if key == .text "j" || key == .text "k" then sourceStart run steps nav jobs else 1)
      nav key lastPage jobs

private partial def wait (draw : Navigation → Nat → Nat → Cli Unit) (lastPage : Nat → Nat → Nat)
    (run : Run) (steps : Array Trace.Step) (refresh : Option Nat) (nav : Navigation)
    (size : Nat × Nat) (jobs : Array BranchObservation) : Cli (Option Navigation) := do
  let key ← Input.read
  if [.text "q", .escape, .interrupt, .eof].contains key then return none
  let nextSize ← request .dimensions
  let next := moved steps run nav key (lastPage nextSize.1 nextSize.2) jobs
  let next := { next with workers := min next.workers (lastPage nextSize.1 nextSize.2) }
  if next != nav || nextSize != size then draw next nextSize.1 nextSize.2
  if refresh.any ((← request .now) ≥ ·) then return some next
  wait draw lastPage run steps refresh next nextSize jobs

private structure View where
  snapshot : Trace.Snapshot := {}
  history : Array History := #[]
  status : String := "connecting"
  timing : Option Timing.Run := none
  timingAvailable : Bool := false
  jobs : Array BranchObservation := #[]

private def loadView (ctx : Context) (run : Run) (previous : View) (interactive : Bool) : Cli View := do
  let status ← status ctx run
  let observed ← observing (ctx.observation run)
  let timing ← match observed with
    | .ok value => pure value.timing
    | .error _ => ctx.savedTiming run
  let jobs := observed.toOption.map (fun value => value.jobs.map BranchObservation.ofJob)
    |>.getD previous.jobs
  let timingAvailable := observed.isOk
  let live := status == "result pending"
  let snapshot ← Trace.load ctx run (if live && interactive then some previous.snapshot.cursors else none)
  -- Trace already fetched the inventory; do not ask every node a second time.
  let history := if live then
    (snapshot.nodes.filter (·.id != "scheduler")).map fun node =>
      { name := ctx.node node.id, resources := node.samples, fresh := node.online : History }
    else previous.history
  return { snapshot, status, timing, timingAvailable, history, jobs }

private def drawView (ctx : Context) (run : Run) (view : View) (interactive color : Bool)
    (nav : Navigation) (width height : Nat) : Cli Unit := do
  let lines := frame ctx run view.snapshot.steps view.history nav width height
    view.status color view.snapshot.warning view.timing view.jobs
  if interactive then request (.write "\x1b[H\x1b[2J")
  request (.write (String.intercalate "\n" lines.toList ++ "\n"))
  request .flush

private def lastPage (ctx : Context) (view : View) (width height : Nat) : Nat :=
  let width := width - 1
  let sidebar := width ≥ 100
  let bodyWidth := if sidebar then width - min 52 (max 38 (width / 4)) - 3 else width
  let bodyHeight := height - 5 - (if sidebar then 0 else 5)
  let roster := workerRoster ctx view.snapshot.steps view.history
  let count := roster.size
  let height := bodyHeight - 3 - groupCodeRows bodyHeight
  let entries := BranchTree.current view.snapshot.steps view.jobs
  let cellHeight := workerCardHeight view.snapshot.steps entries roster (view.status == "result pending") height
  let capacity := workerCapacity count bodyWidth height cellHeight
  (count + capacity - 1) / capacity - 1

private partial def loop (ctx : Context) (run : Run) (interactive color : Bool)
    (previous : View) (nav : Navigation := {}) : Cli Unit := do
  let (width, height) ← if interactive then request .dimensions else pure (120, 35)
  let fetched ← if !interactive then
    pure (some (← loadView ctx run previous false, (nav, (width, height))))
  else
    Fetch.run (loadView ctx run previous true) (fun (nav, size) => do
      let key ← Input.read
      if [.text "q", .escape, .interrupt, .eof].contains key then return none
      let nextSize ← request .dimensions
      let next := moved previous.snapshot.steps run nav key (lastPage ctx previous nextSize.1 nextSize.2) previous.jobs
      if next != nav || nextSize != size then
        drawView ctx run previous true color next nextSize.1 nextSize.2
      return some (next, nextSize)) (nav, (width, height))
  let some (view, (nav, (width, height))) := fetched | return
  let draw := drawView ctx run view interactive color
  draw nav width height
  if !interactive then return
  let now ← request .now
  let awaitingTiming := view.timingAvailable && view.timing.any (fun timing => timing.span.any (·.finishedMs.isNone))
  let refresh := if terminal view.status && !awaitingTiming then none else some (now + 1000)
  let some nav ← wait draw (lastPage ctx view) run view.snapshot.steps refresh nav (width, height) view.jobs | return
  loop ctx run interactive color view nav

/-- Watching is an Eff program and never submits or resumes a workflow. -/
def run (ctx : Context) (id : String) (once := false) : Cli Unit := do
  validateId id
  let run ← try ctx.loadRun id catch error => do
    let path := ctx.directory id / "run.json"
    unless (← ctx.connection).isSome && (← request (.exists path)) do throw error
    let saved ← readJson (α := Run) path
    unless saved.id == id do throw "Run manifest mismatch"
    printLine "Deployment unavailable; showing the saved workflow view."
    pure saved
  let interactive ← if once then pure false else request .enterTerminal
  try
    if interactive then request (.write "\x1b[?1049h\x1b[?25l")
    let color := interactive && (← colorsEnabled)
    let initial : View := { snapshot := ← Trace.retain ctx run {} }
    if interactive then
      let (width, height) ← request .dimensions
      drawView ctx run initial true color {} width height
    loop ctx run interactive color initial
  finally
    if interactive then
      try request .leaveTerminal
      finally
        request (.write "\x1b[?25h\x1b[?1049l")
        request .flush

end LeanCloudCli.Watch
