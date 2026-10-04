import LeanCloudCli.Console
import LeanCloudCli.Completion
import LeanCloudCli.Input

namespace LeanCloudCli.Shell
open LeanEff

structure Cycle where
  original : String
  context : Completion.Context
  items : Array Completion.Item
  selected : Nat

structure State where
  line : String := ""
  cursor : Nat := 0
  history : Array String := #[]
  browsing : Option Nat := none
  draft : String := ""
  transcript : Array Styled.Line := #[]
  partialLine : String := ""
  scroll : Nat := 0
  cycle : Option Cycle := none

def appendOutput (state : State) (text : String) (color : Styled.Color := .normal) : State := Id.run do
  let lines := (state.partialLine ++ text).splitOn "\n"
  let mut all := state.transcript ++ (lines.dropLast.map (fun line => Styled.text (safe line) color)).toArray
  let mut partialLine := safe (lines.getLast!)
  -- A program can emit an unbounded line; keep the transcript bounded too.
  while partialLine.length > 4096 do
    all := all.push (Styled.text (String.ofList (partialLine.toList.take 4096)) color)
    partialLine := String.ofList (partialLine.toList.drop 4096)
  let removed := all.size - 2000
  let added := all.size - state.transcript.size
  return { state with
    transcript := all.extract removed all.size, partialLine
    scroll := if state.scroll == 0 then 0 else state.scroll + added }

def appendStyled (state : State) (line : Styled.Line) : State :=
  let state := if state.partialLine.isEmpty then state else appendOutput state "\n"
  let all := state.transcript.push (Styled.slice line 0 4096)
  { state with
    transcript := all.extract (all.size - 2000) all.size
    scroll := if state.scroll == 0 then 0 else state.scroll + 1 }

private def replace (state : State) (start stop : Nat) (text : String) : State :=
  { state with
    line := String.ofList (state.line.toList.take start) ++ text ++ String.ofList (state.line.toList.drop stop)
    cursor := start + text.length, cycle := none, browsing := none }

def complete (catalog : Completion.Catalog) (state : State) (backward := false) : State := Id.run do
  let cycle := match state.cycle with
    | some cycle => { cycle with selected :=
        (cycle.selected + (if backward then cycle.items.size - 1 else 1)) % max 1 cycle.items.size }
    | none =>
      let context := Completion.context state.line state.cursor
      let items := Completion.candidates catalog context
      { original := state.line, context, items, selected := if backward then items.size - 1 else 0 }
  let some item := cycle.items[cycle.selected]? | return state
  let (line, cursor) := Completion.apply cycle.original cycle.context item
  if cycle.items.size == 1 && cursor == line.length then
    let space := if item.value.endsWith "/" then "" else " "
    return { state with line := line ++ space, cursor := cursor + space.length, cycle := none }
  return { state with line, cursor, cycle := some cycle }

def edit (catalog : Completion.Catalog) (state : State) (key : Input.Key) : State :=
  match key with
  | .text text => replace state state.cursor state.cursor text
  | .backspace => if state.cursor == 0 then state else replace state (state.cursor - 1) state.cursor ""
  | .delete | .eof => replace state state.cursor (state.cursor + 1) ""
  | .left => { state with cursor := state.cursor - 1, cycle := none }
  | .right => { state with cursor := min state.line.length (state.cursor + 1), cycle := none }
  | .home => { state with cursor := 0, cycle := none }
  | .end => { state with cursor := state.line.length, cycle := none }
  | .clear | .interrupt => { state with line := "", cursor := 0, cycle := none, browsing := none }
  | .killEnd => replace state state.cursor state.line.length ""
  | .escape => { state with cycle := none }
  | .tab => complete catalog state
  | .backTab => complete catalog state true
  | .up =>
    let index := state.browsing.map (· - 1) |>.getD (state.history.size - 1)
    match state.history[index]? with
    | none => state
    | some line =>
      let draft := if state.browsing.isNone then state.line else state.draft
      { state with line, cursor := line.length, browsing := some index, draft, cycle := none }
  | .down =>
    match state.browsing with
    | none => state
    | some index =>
      let line := state.history[index + 1]?.getD state.draft
      let browsing := if index + 1 < state.history.size then some (index + 1) else none
      { state with line, cursor := line.length, cycle := none, browsing }
  | .pageUp => { state with scroll := state.scroll + 10 }
  | .pageDown => { state with scroll := state.scroll - 10 }
  | _ => state

structure Frame where
  lines : Array String
  promptRow : Nat
  cursorColumn : Nat
  deriving Repr

private def outputLines (state : State) (width : Nat) : Array Styled.Line :=
  (state.transcript ++ (if state.partialLine.isEmpty then #[] else #[Styled.text state.partialLine])).flatMap fun line =>
    (Array.range (max 1 ((Styled.length line + width - 1) / width))).map fun i =>
      Styled.slice line (i * width) ((i + 1) * width)

private def clampScroll (state : State) (columns rows : Nat) : State :=
  let count := (outputLines state (max 1 (columns - 1))).size
  { state with scroll := min state.scroll (count - (rows - 5)) }

/-- The last two rows belong to completion and hints, immediately below the prompt. -/
def frame (project : String) (catalog : Completion.Catalog) (state : State)
    (columns rows : Nat) (busy := false) (color := false) : Frame := Id.run do
  let width := max 1 (columns - 1) -- avoid terminal autowrap in the last column
  let height := max 1 rows
  let promptRow := max 1 (height - 2)
  let mut lines := Array.replicate height (#[] : Styled.Line)
  if height ≥ 6 then
    lines := lines.set! 0 (Styled.text (pad width s!" lean-cloud  /  {project}") .header)
    let room := height - 5
    let output := outputLines state width
    let stop := output.size - min state.scroll (output.size - room)
    let visible := output.extract (stop - room) stop
    for (line, i) in visible.toList.zipIdx do lines := lines.set! (i + 1) line
    lines := lines.set! (promptRow - 2) (Styled.text (String.ofList (List.replicate width '─')) .cyan)
  let prompt := if busy then "running> " else "cloud> "
  let room := width - prompt.length
  let start := state.cursor - (room - 1)
  let input := String.ofList (state.line.toList.drop start |>.take room)
  lines := lines.set! (promptRow - 1)
    (Styled.text prompt (if busy then .yellow else .green) ++ Styled.text input)
  let (items, selected) := match state.cycle with
    | some cycle => (cycle.items, cycle.selected)
    | none => (Completion.candidates catalog (Completion.context state.line state.cursor), 0)
  let visible := items.extract (selected - 2) (selected + 6)
  let suggestions := visible.toList.zipIdx |>.foldl (fun spans (item, i) =>
    spans ++ (if i + (selected - 2) == selected then Styled.text ("[" ++ item.value ++ "]") .selected
      else Styled.text item.value .cyan) ++ Styled.text "   ") (Styled.text "  ")
  if promptRow < height then
    lines := lines.set! promptRow (if items.isEmpty then Styled.text "  No completions" .muted else suggestions)
  if promptRow + 1 < height then
    let description := (items[selected]?.map (·.description)).getD ""
    lines := lines.set! (promptRow + 1) (Styled.text (if busy then "  Working · PgUp/PgDn scroll · Ctrl-C interrupt · draft runs only after completion"
      else "  Tab / Shift-Tab complete · ↑↓ history · PgUp/PgDn output" ++
        (if description.isEmpty then "" else " · " ++ description)) .muted)
  return ⟨lines.map (fun line => Styled.render line width color), promptRow, min width (prompt.length + state.cursor - start + 1)⟩

private def draw (ctx : Context) (catalog : Completion.Catalog) (state : State)
    (size : Nat × Nat) (busy := false) : Cli Unit := do
  let view := frame ctx.project catalog state size.1 size.2 busy (← colorsEnabled)
  let mut output := "\x1b[?25l"
  for (line, index) in view.lines.toList.zipIdx do
    output := output ++ s!"\x1b[{index + 1};1H\x1b[2K" ++ line
  output := output ++ s!"\x1b[{view.promptRow};{view.cursorColumn}H\x1b[?25h"
  request (.write output)
  request .flush

/-- Handle command output in Eff, feeding the transcript instead of writing over
    the prompt. All other host requests retain their ordinary continuations. -/
partial def execute (ctx : Context) (catalog : Completion.Catalog) (state : State)
    (program : Cli (Context × Bool)) (lastSize : Nat × Nat := (0, 0)) : Cli (Except String (Context × Bool) × State) := do
  match program.run with
  | .pure result => return (result, state)
  | .impure (.here (.request (.write text stderr))) next =>
    let state := appendOutput state text (if stderr then .red else .normal)
    let result ← observing do
      let size ← request .dimensions
      draw ctx catalog state size true
      return size
    execute ctx catalog state (ExceptT.mk (ArrsF.apply next (result.map fun _ => ())))
      (result.toOption.getD lastSize)
  | .impure (.here (.request (.writeStyled line))) next =>
    let state := appendStyled state line
    let result ← observing do
      let size ← request .dimensions
      draw ctx catalog state size true
      return size
    execute ctx catalog state (ExceptT.mk (ArrsF.apply next (result.map fun _ => ())))
      (result.toOption.getD lastSize)
  | .impure (.here (.request (.pollProcess id timeout))) next =>
    let chunk ← observing (request (.pollProcess id timeout))
    let result ← observing do
      let chunk ← liftExcept chunk
      if chunk.exitCode.isNone then
        let key ← Input.read 0
        if key == .interrupt then throw "Local command interrupted. Use 'status' to inspect services already started."
        let size ← request .dimensions
        let state := clampScroll (edit catalog state key) size.1 size.2
        if key != .idle || size != lastSize then draw ctx catalog state size true
        return (chunk, state, size)
      return (chunk, state, lastSize)
    let state := result.toOption.map (·.2.1) |>.getD state
    let size := result.toOption.map (·.2.2) |>.getD lastSize
    execute ctx catalog state (ExceptT.mk (ArrsF.apply next (result.map Prod.fst))) size
  | .impure (.here (.request operation)) next =>
    let result ← observing (request operation)
    execute ctx catalog state (ExceptT.mk (ArrsF.apply next result)) lastSize
  | .impure (.there rest) _ => nomatch rest

private def screenOn : Cli Unit := request (.write "\x1b[?1049h\x1b[?2004h\x1b[H\x1b[2J")
private def screenOff : Cli Unit := do
  request (.write "\x1b[0m\x1b[?25h\x1b[?2004l\x1b[?1049l")
  request .flush

private def submit (ctx : Context) (catalog : Completion.Catalog) (state : State) : Cli (Context × Bool × State) := do
  let line := state.line.trimAscii.toString
  if line.isEmpty then return (ctx, true, { state with line := "", cursor := 0, cycle := none })
  let state := appendStyled state (Styled.text "cloud> " .green ++ Styled.text line)
  let state := { state with line := "", cursor := 0, cycle := none, browsing := none, draft := "" }
  draw ctx catalog state (← request .dimensions) true
  let (result, state) ← match words line with
    | .error error => pure (.error error, state)
    | .ok args =>
      if args == ["top"] || (args.length == 2 && args.head? == some "watch") then do
        -- Give the live view terminal ownership, then rebuild the shell screen.
        screenOff
        request .leaveTerminal
        let result ← observing (dispatch ctx args)
        let active ← request .enterTerminal
        unless active do throw "Could not restore the interactive terminal"
        screenOn
        pure (result, state)
      else execute ctx catalog state (dispatch ctx args)
  let state := match result with
    | .error error => appendStyled state (Styled.text ("Error: " ++ error) .red)
    | .ok _ => state
  let history := if state.history.back? == some line then state.history else state.history.push line
  let history := history.extract (history.size - 500) history.size
  let state := { state with history }
  let (ctx, keepGoing) := result.toOption.getD (ctx, true)
  return (ctx, keepGoing, state)

private partial def loop (ctx : Context) (catalog : Completion.Catalog) (state : State)
    (lastSize : Nat × Nat := (0, 0)) (redraw := true) : Cli Unit := do
  let catalog ← if redraw then Completion.refreshFiles ctx catalog state.line state.cursor else pure catalog
  let size ← request .dimensions
  let state := clampScroll state size.1 size.2
  if redraw || size != lastSize then draw ctx catalog state size
  let key ← Input.read
  match key with
  | .eof | .interrupt =>
    if state.line.isEmpty then return
    loop ctx catalog (edit catalog state key) size
  | .enter =>
    let (ctx, keepGoing, state) ← submit ctx catalog state
    if keepGoing then loop ctx (← Completion.load ctx) state size
  | .idle => loop ctx catalog state size false
  | _ => loop ctx catalog (edit catalog state key) size

/-- Called after acquiring the terminal; always restores the screen and terminal. -/
def run (ctx : Context) : Cli Unit := do
  try
    screenOn
    let catalog ← Completion.load ctx
    loop ctx catalog { transcript := #[Styled.text "Cloud programs, processes and workers." .cyan,
      Styled.text "Type a command or press Tab to complete. Use help for all commands." .muted, #[]] }
  finally
    try request .leaveTerminal finally screenOff

end LeanCloudCli.Shell
