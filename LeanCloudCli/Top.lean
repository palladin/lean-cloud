import LeanCloudCli.Monitor
import LeanCloudCli.SnapshotMetrics
import LeanCloudCli.Input

namespace LeanCloudCli.Top

/-- The deployment API supplies the compute-node inventory. -/
def actors (nodes : Array Node) : Array Node :=
  nodes.qsort fun a b =>
      if (a.state == "running") != (b.state == "running") then a.state == "running"
      else if a.role == "scheduler" || b.role == "scheduler" then
        if a.role == b.role then a.name < b.name else a.role == "scheduler"
      else if workerIndex? a.role != workerIndex? b.role then
        (workerIndex? a.role).getD 0 < (workerIndex? b.role).getD 0
      else a.name < b.name

private def columnCount (width : Nat) : Nat := max 1 (min 3 ((width - 1) / 55))

private def cardHeight := 12

def pageSize (width height : Nat) : Nat := columnCount width * max 1 ((height - 4) / cardHeight)

def pageCount (nodes : Array Node) (width height : Nat) : Nat :=
  max 1 ((nodes.size + pageSize width height - 1) / pageSize width height)

private def visible (nodes : Array Node) (page width height : Nat) : Array Node :=
  let start := min page (pageCount nodes width height - 1) * pageSize width height
  nodes.extract start (start + pageSize width height)

private def panel (node : Node) (width : Nat) : Array Styled.Line :=
  #[Styled.text (pad width s!" {node.role} · shared pool") .selected,
    Styled.text (node.state ++ " ") (Styled.statusColor node.state) ++ Styled.text node.name .muted] ++
    (if node.state == "running" then SnapshotMetrics.lines (node.resources.getD #[]) width
     else #[Styled.text "No live samples; node is unavailable" .muted])

/-- Pure, paged resource dashboard. Width includes the unused final terminal column. -/
def frame (project : String) (nodes : Array Node) (page width height : Nat)
    (color := false) (warning := "") : Array String := Id.run do
  let columns := columnCount width
  let room := width - 1
  let cellWidth := (room - (columns - 1) * 3) / columns
  let page := min page (pageCount nodes width height - 1)
  let mut lines := #[Styled.text (pad room s!" lean-cloud / {project} / top · {(nodes.filter (·.state == "running")).size}/{nodes.size} running") .header,
    Styled.text s!"q: back · PgUp/PgDn or ←/→: page · {page + 1}/{pageCount nodes width height}" .cyan]
  if width < 40 || height < 16 then
    lines := lines.push (Styled.text "Enlarge terminal to at least 40 × 16 for graphs." .yellow)
  else if nodes.isEmpty then
    lines := lines.push (Styled.text "No workers or schedulers reported by the deployment API." .muted)
  else
    let cards := (visible nodes page width height).map fun node =>
      panel node cellWidth
    for row in [:((cards.size + columns - 1) / columns)] do
      for line in [:cardHeight] do
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
    Styled.text "CPU 100%=1 logical CPU; bars use container capacity (+ overflow). I/O and network show rates." .muted
    else Styled.text warning .yellow)
  return (lines.extract 0 (height - 1)).map (fun line => Styled.render line room color)

private def draw (ctx : Context) (nodes : Array Node)
    (page width height : Nat) (interactive color : Bool) (warning : String) : Cli Unit := do
  if interactive then request (.write "\x1b[H\x1b[2J")
  request (.write (String.intercalate "\n" (frame ctx.project nodes page width height color warning).toList ++ "\n"))
  request .flush

private partial def wait (ctx : Context) (nodes : Array Node)
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
    draw ctx nodes nextPage nextSize.1 nextSize.2 true color warning
  wait ctx nodes nextPage nextSize refreshAt color warning

private partial def loop (ctx : Context) (interactive color : Bool)
    (page : Nat := 0) : Cli Unit := do
  let nodes := actors (← ctx.nodes)
  let warning := String.intercalate "; " ((nodes.filter (!·.warning.isEmpty)).map fun n => n.role ++ ": " ++ n.warning).toList
  let (width, height) ← if interactive then request .dimensions else pure (120, 35)
  let page := min page (pageCount nodes width height - 1)
  if !interactive then
    for page in [:pageCount nodes width height] do
      draw ctx nodes page width height false false warning
    return
  draw ctx nodes page width height true color warning
  let some page ← wait ctx nodes page (width, height) ((← request .now) + 1000) color warning | return
  loop ctx interactive color page

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
