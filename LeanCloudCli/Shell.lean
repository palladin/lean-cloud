import LeanCloudCli.Console
import LeanCloudCli.Completion
import LeanCloudCli.Input
import LeanCloudCli.Shell.Transcript

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
  cycle : Option Cycle := none
  transcript : Transcript := {}
  notice : String := ""
  painted : Array String := #[]
  paintedSize : Nat × Nat := (0, 0)

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
  | _ => state

/-- The output viewport and footer share a frame, but have independent positions. -/
structure Frame where
  lines : Array String
  promptRow : Nat
  cursorColumn : Nat
  deriving Repr

private def footerHeight (rows : Nat) := min 4 (rows - 1)
private def outputRows (rows : Nat) := max 1 (rows - footerHeight rows)

def frame (project : String) (catalog : Completion.Catalog) (state : State)
    (columns rows : Nat) (busy := false) (color := false) : Frame := Id.run do
  let width := max 1 (columns - 1)
  let height := footerHeight rows
  let firstRow := outputRows rows + 1
  let promptRow := firstRow + if height == 4 then 1 else 0
  let transcript := state.transcript.resize width
  let output := transcript.visible (outputRows rows)
  let mut lines := output ++ Array.replicate (outputRows rows - output.size) #[]
  let mut footer := #[]
  if height == 4 then
    let position := if transcript.top.isSome then " · older output · click here for latest" else ""
    footer := footer.push (Styled.text (pad width s!" lean-cloud  /  {project}{position}") .header)
  let prompt := if busy then "running> " else "cloud> "
  let room := width - prompt.length
  let start := state.cursor - (room - 1)
  let input := String.ofList (state.line.toList.drop start |>.take room)
  if height > 0 then
    footer := footer.push (Styled.text prompt (if busy then .yellow else .green) ++ Styled.text input)
  let (items, selected) := match state.cycle with
    | some cycle => (cycle.items, cycle.selected)
    | none => (Completion.candidates catalog (Completion.context state.line state.cursor), 0)
  let visible := items.extract (selected - 2) (selected + 6)
  let suggestions := visible.toList.zipIdx |>.foldl (fun spans (item, i) =>
    spans ++ (if i + (selected - 2) == selected then Styled.text ("[" ++ item.value ++ "]") .selected
      else Styled.text item.value .cyan) ++ Styled.text "   ") (Styled.text "  ")
  if footer.size < height then
    footer := footer.push (if items.isEmpty then Styled.text "  No completions" .muted else suggestions)
  if footer.size < height then
    let hint := if !state.notice.isEmpty then state.notice
      else if transcript.hasSelection then "Ctrl-C copy selection · Esc clear · wheel scroll"
      else if busy then "Wheel scroll · drag copies · Ctrl-A all · Ctrl-C interrupt"
      else "Wheel scroll · drag copies · Ctrl-A all · Tab complete · ↑↓ history"
    footer := footer.push (Styled.text ("  " ++ hint) .muted)
  lines := lines ++ footer
  return ⟨lines.mapIdx (fun index line =>
      Styled.render line (if index < outputRows rows then Styled.length line else width) color),
    min (max 1 rows) promptRow, min width (prompt.length + state.cursor - start + 1)⟩

private def draw (ctx : Context) (catalog : Completion.Catalog) (state : State)
    (size : Nat × Nat) (busy := false) : Cli State := do
  let state := { state with transcript := state.transcript.resize (size.1 - 1) }
  let view := frame ctx.project catalog state size.1 size.2 busy (← colorsEnabled)
  let mut output := "\x1b[?2026h\x1b[?25l"
  for (line, index) in view.lines.toList.zipIdx do
    if size != state.paintedSize || state.painted[index]? != some line then
      output := output ++ s!"\x1b[{index + 1};1H\x1b[2K" ++ line
  output := output ++ s!"\x1b[{view.promptRow};{view.cursorColumn}H\x1b[?25h\x1b[?2026l"
  request (.write output)
  request .flush
  return { state with painted := view.lines, paintedSize := size }

private def copySelection (state : State) : Cli State := do
  let text := state.transcript.selectedText
  if text.isEmpty then return state
  let result ← observing (request (.copyClipboard text))
  return { state with notice := match result with
    | .ok _ => s!"Copied {text.length} characters · Esc clear selection"
    | .error error => s!"Could not copy: {error}" }

/-- Mouse input changes the output pane, never the command draft. -/
def handleKey (catalog : Completion.Catalog) (state : State) (key : Input.Key)
    (size : Nat × Nat) : Cli State := do
  let transcript := state.transcript.resize (size.1 - 1)
  let state := { state with transcript, notice := "" }
  let height := outputRows size.2
  match key with
  | .idle => return state
  | .scrollTop => return { state with transcript := { transcript with top := some 0 } }
  | .scrollBottom => return { state with transcript := { transcript with top := none } }
  | .pageUp | .pageDown =>
    return { state with transcript := transcript.scroll height (key == .pageUp) (max 1 (height / 2)) }
  | .selectAll =>
    if state.line.isEmpty then return { state with transcript := transcript.selectAll }
    else return edit catalog state .home
  | .interrupt =>
    if transcript.hasSelection then copySelection state
    else return edit catalog state key
  | .mouse event =>
    if event.button / 64 % 2 == 1 then
      if event.released || event.button % 4 > 1 then return state
      return { state with transcript := transcript.scroll height (event.button % 2 == 0) 3 }
    if event.released then
      if let some selection := transcript.selection then
        if selection.dragging then
          let focus := transcript.positionAt height (event.row - 1) (event.column - 1)
          return ← copySelection { state with transcript := { transcript with
            selection := some { selection with focus, dragging := false } } }
      return state
    if event.button % 4 != 0 then return state
    if event.button / 32 % 2 == 1 then
      let some selection := transcript.selection | return state
      unless selection.dragging do return state
      let transcript := if event.row > height then transcript.scroll height false 1
        else if event.row == 1 then transcript.scroll height true 1 else transcript
      let focus := transcript.positionAt height (event.row - 1) (event.column - 1)
      return { state with transcript := { transcript with selection := some { selection with focus } } }
    if event.row == height + 1 then
      return { state with transcript := { transcript with top := none, selection := none } }
    if event.row > height then return state
    let position := transcript.positionAt height (event.row - 1) (event.column - 1)
    let transcript := { transcript with
      top := some (transcript.visibleStart height), selection := some ⟨position, position, true⟩ }
    return { state with transcript }
  | _ => return edit catalog { state with transcript := { transcript with selection := none } } key

/-- Interpret command output and input in Eff; the host only draws and polls. -/
partial def execute (ctx : Context) (catalog : Completion.Catalog) (state : State)
    (program : Cli (Context × Bool)) (lastSize : Nat × Nat := (0, 0)) : Cli (Except String (Context × Bool) × State) := do
  match program.run with
  | EffF.pure _ result => return (result, state)
  | EffF.impure _ (.here (.request (.write text stderr))) next =>
    let state := { state with transcript := state.transcript.append text (if stderr then .red else .normal) }
    let result ← observing do
      let size ← request .dimensions
      let state ← draw ctx catalog state size true
      return (state, size)
    execute ctx catalog (result.toOption.map Prod.fst |>.getD state)
      (ExceptT.mk (ArrsF.apply next (result.map fun _ => ())))
      (result.toOption.map Prod.snd |>.getD lastSize)
  | EffF.impure _ (.here (.request (.writeStyled line))) next =>
    let state := { state with transcript := state.transcript.appendStyled line }
    let result ← observing do
      let size ← request .dimensions
      let state ← draw ctx catalog state size true
      return (state, size)
    execute ctx catalog (result.toOption.map Prod.fst |>.getD state)
      (ExceptT.mk (ArrsF.apply next (result.map fun _ => ())))
      (result.toOption.map Prod.snd |>.getD lastSize)
  | EffF.impure _ (.here (.request operation)) next =>
    let result ← observing (request operation)
    execute ctx catalog state (ExceptT.mk (ArrsF.apply next result)) lastSize
  | EffF.impure _ (.there rest) _ => nomatch rest

private def screenOn : Cli Unit :=
  request (.write "\x1b[?1049h\x1b[r\x1b[?2004h\x1b[?1002h\x1b[?1006h\x1b[H\x1b[2J")

private def screenOff : Cli Unit := do
  request (.write "\x1b[?2026l\x1b[r\x1b[0m\x1b[?25h\x1b[?1002l\x1b[?1006l\x1b[?2004l\x1b[?1049l")
  request .flush

private def submit (ctx : Context) (catalog : Completion.Catalog) (state : State) : Cli (Context × Bool × State) := do
  let line := state.line.trimAscii.toString
  if line.isEmpty then return (ctx, true, { state with line := "", cursor := 0, cycle := none })
  let transcript := { state.transcript with top := none, selection := none }
  let transcript := transcript.appendStyled (Styled.text "cloud> " .green ++ Styled.text line)
  let state := { state with line := "", cursor := 0, cycle := none, browsing := none, draft := "", transcript, notice := "" }
  let state ← draw ctx catalog state (← request .dimensions) true
  let (result, state) ← match words line with
    | .error error => pure (.error error, state)
    | .ok args =>
      if !Help.requested args && (args == ["top"] || (args.length == 2 && args.head? == some "watch")) then do
        -- Each live monitor owns terminal modes while it runs.
        screenOff
        request .leaveTerminal
        let result ← observing (dispatch ctx args)
        let active ← request .enterTerminal
        unless active do throw "Could not restore the interactive terminal"
        screenOn
        pure (result, { state with painted := #[], paintedSize := (0, 0) })
      else execute ctx catalog state (dispatch ctx args) (← request .dimensions)
  let state := match result with
    | .error error => { state with transcript := state.transcript.appendStyled (Styled.text ("Error: " ++ error) .red) }
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
  let state ← if redraw || size != lastSize then draw ctx catalog state size else pure state
  let key ← Input.read
  match key with
  | .interrupt =>
    if state.transcript.hasSelection then
      loop ctx catalog (← handleKey catalog state key size) size
    else if state.line.isEmpty then return
    else loop ctx catalog (edit catalog state key) size
  | .eof =>
    if state.line.isEmpty then return
    loop ctx catalog (edit catalog state key) size
  | .enter =>
    let (ctx, keepGoing, state) ← submit ctx catalog state
    if keepGoing then loop ctx (← Completion.load ctx) state size
  | .idle => loop ctx catalog state size false
  | _ => loop ctx catalog (← handleKey catalog state key size) size

/-- Called after acquiring the terminal; always restores the screen and terminal. -/
def run (ctx : Context) : Cli Unit := do
  try
    let size ← request .dimensions
    screenOn
    let catalog ← Completion.load ctx
    let transcript := ({} : Transcript)
      |>.appendStyled (Styled.text "Cloud programs, processes and workers." .cyan)
      |>.appendStyled (Styled.text "Type a command or press Tab to complete. Use help for all commands." .muted)
      |>.appendStyled #[]
    let state ← draw ctx catalog { transcript } size
    loop ctx catalog state size false
  finally
    try request .leaveTerminal finally screenOff

end LeanCloudCli.Shell
