import LeanCloudCli.Monitor
import LeanCloudCli.Input

namespace LeanCloudCli.Top

/-- Compute nodes only. Mailbox brokers and blob services remain in `nodes`. -/
def actors (nodes : Array Node) : Array Node :=
  (nodes.filter (fun node =>
    (isActor node.role))).qsort fun a b =>
      if (a.state == "running") != (b.state == "running") then a.state == "running"
      else if a.role == "scheduler" || b.role == "scheduler" then
        if a.role == b.role then a.name < b.name else a.role == "scheduler"
      else if workerIndex? a.role != workerIndex? b.role then
        (workerIndex? a.role).getD 0 < (workerIndex? b.role).getD 0
      else a.name < b.name

private def columnCount (width : Nat) : Nat := max 1 (min 3 ((width - 1) / 55))

def pageSize (width height : Nat) : Nat := columnCount width * max 1 ((height - 4) / 10)

def pageCount (nodes : Array Node) (width height : Nat) : Nat :=
  max 1 ((nodes.size + pageSize width height - 1) / pageSize width height)

private def visible (nodes : Array Node) (page width height : Nat) : Array Node :=
  let start := min page (pageCount nodes width height - 1) * pageSize width height
  nodes.extract start (start + pageSize width height)

private def panel (node : Node) (history : Array History) (disk : Option DiskUsage)
    (width : Nat) : Array Styled.Line :=
  let points := history.find? (fun h => h.name == node.name && h.fresh &&
    h.points.back?.map (·.session) == some node.started)
  #[Styled.text (pad width s!" {node.role} · {node.run.getD "shared pool"}") .selected,
    Styled.text (node.state ++ " ") (Styled.statusColor node.state) ++ Styled.text node.name .muted] ++
    (if node.state == "running" then metricLines (points.map (·.points) |>.getD #[]) width disk
     else #[Styled.text "No live samples; process is stopped" .muted])

/-- Pure, paged resource dashboard. Width includes the unused final terminal column. -/
def frame (project : String) (nodes : Array Node) (history : Array History)
    (disks : Array (String × DiskUsage)) (page width height : Nat)
    (color := false) (warning := "") : Array String := Id.run do
  let columns := columnCount width
  let room := width - 1
  let cellWidth := (room - (columns - 1) * 3) / columns
  let page := min page (pageCount nodes width height - 1)
  let mut lines := #[Styled.text (pad room s!" lean-cloud / {project} / top · {(nodes.filter (·.state == "running")).size}/{nodes.size} running") .header,
    Styled.text s!"q: back · PgUp/PgDn or ←/→: page · {page + 1}/{pageCount nodes width height}" .cyan]
  if width < 40 || height < 14 then
    lines := lines.push (Styled.text "Enlarge terminal to at least 40 × 14 for graphs." .yellow)
  else if nodes.isEmpty then
    lines := lines.push (Styled.text "No workers or schedulers. Use 'deploy' or 'up' to start the nodes." .muted)
  else
    let cards := (visible nodes page width height).map fun node =>
      panel node history ((disks.find? (·.1 == node.name)).map (·.2)) cellWidth
    for row in [:((cards.size + columns - 1) / columns)] do
      for line in [:10] do
        let mut combined : Styled.Line := #[]
        for column in [:columns] do
          if column > 0 then combined := combined ++ Styled.text " │ " .muted
          let content := (cards[row * columns + column]?.getD #[])[line]?.getD #[]
          -- Keep styles through clipping and pad columns without counting ANSI bytes.
          let content := if Styled.length content > cellWidth then
            Styled.slice content 0 (cellWidth - 1) ++ Styled.text "…" .muted else content
          combined := combined ++ content ++
            Styled.text (String.ofList (List.replicate (cellWidth - Styled.length content) ' '))
        lines := lines.push combined
  lines := lines.push (if warning.isEmpty then
    Styled.text "CPU 100%=1 core (+ overflow); I/O and network show rates; — needs samples." .muted
    else Styled.text warning .yellow)
  return (lines.extract 0 (height - 1)).map (fun line => Styled.render line room color)

private def draw (ctx : Context) (nodes : Array Node) (history : Array History)
    (page width height : Nat) (interactive color : Bool) (warning : String) : Cli Unit := do
  let mut disks := #[]
  if width ≥ 40 && height ≥ 14 then
    for node in visible nodes page width height do
      -- A node can exit between inventory and `df`; keep the dashboard usable.
      let disk ← try filesystem node catch _ => pure none
      if let some disk := disk then disks := disks.push (node.name, disk)
  if interactive then request (.write "\x1b[H\x1b[2J")
  request (.write (String.intercalate "\n" (frame ctx.project nodes history disks page width height color warning).toList ++ "\n"))
  request .flush

private partial def wait (ctx : Context) (nodes : Array Node) (history : Array History)
    (page : Nat) (size : Nat × Nat) (refreshAt : Nat) (color : Bool) (warning : String)
    : Cli (Option Nat) := do
  let key ← Input.read
  if [.text "q", .escape, .interrupt, .eof].contains key then return none
  let nextSize ← request .dimensions
  let pages := pageCount nodes nextSize.1 nextSize.2
  let nextPage := min (match key with
    | .pageDown | .right | .tab => min (page + 1) (pages - 1)
    | .pageUp | .left | .backTab => page - 1
    | .home => 0
    | .end => pages - 1
    | _ => page) (pages - 1)
  if (← request .now) ≥ refreshAt then return some nextPage
  if nextPage != page || nextSize != size then
    draw ctx nodes history nextPage nextSize.1 nextSize.2 true color warning
  wait ctx nodes history nextPage nextSize refreshAt color warning

private partial def loop (ctx : Context) (interactive color : Bool)
    (history : Array History := #[]) (page : Nat := 0) : Cli Unit := do
  let nodes := actors (← ctx.nodes)
  let values ← observing (samples nodes)
  let warning := match values with
    | .ok _ => ""
    | .error error => "Stats unavailable: " ++ safe error
  let history := remember (history.filter (fun h => nodes.any (·.name == h.name))) (values.toOption.getD #[])
  let (width, height) ← if interactive then request .dimensions else pure (120, 35)
  let page := min page (pageCount nodes width height - 1)
  if !interactive then
    for page in [:pageCount nodes width height] do
      draw ctx nodes history page width height false false warning
    return
  draw ctx nodes history page width height true color warning
  let some page ← wait ctx nodes history page (width, height) ((← request .now) + 1000) color warning | return
  loop ctx interactive color history page

/-- The same Eff dashboard powers shell, one-shot, and pure-model execution. -/
def run (ctx : Context) (once := false) : Cli Unit := do
  let interactive ← if once then pure false else request .enterTerminal
  try
    if interactive then request (.write "\x1b[?1049h\x1b[?25l")
    loop ctx interactive (interactive && (← colorsEnabled))
  finally
    if interactive then
      try request .leaveTerminal
      finally
        request (.write "\x1b[0m\x1b[?25h\x1b[?1049l")
        request .flush

end LeanCloudCli.Top
