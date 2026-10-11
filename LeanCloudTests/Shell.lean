import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open LeanCloudCli

private def keyBytes (text : String) : List UInt32 := text.toUTF8.data.toList.map (·.toUInt32)

private def suggestions (line : String) : Array String :=
  (Completion.candidates { programs := #[⟨"squares/v1", "Squares"⟩], runs := #[⟨"demo", "squares/v1"⟩], actors := #[⟨"worker1", ""⟩, ⟨"worker2", ""⟩, ⟨"worker3", ""⟩] }
    (Completion.context line line.length)).map (·.value)

def shellCases : Array TestCase := #[
  ⟨"console.shell.contextual-completions", do
    assertEq (suggestions "wa") #["watch"]
    assertEq (suggestions "run sq") #["squares/v1"]
    assertEq (suggestions "inspect de") #["demo"]
    assertEq (suggestions "pa") #["pause"]
    assertEq (suggestions "ki") #["kill"]
    for command in ["pause", "kill", "resume"] do
      assertEq (suggestions (command ++ " de")) #["demo"]
    assertEq (suggestions "watch demo --") #["--once", "--help"]
    assertEq (suggestions "logs demo wo") #["worker1", "worker2", "worker3"]
    assertEq (suggestions "run squares/v1 --input file.json --") #["--id", "--help"]
    assertEq (suggestions "run squares/v1 --id ") #[]⟩,
  ⟨"console.shell.completion-cycles", do
    let start : Shell.State := { line := "r", cursor := 1 }
    let first := Shell.complete {} start
    let second := Shell.complete {} first
    assertEq first.line "remove"
    assertEq second.line "run"
    assertEq (Shell.complete {} second true).line "remove"
    let unique := Shell.complete {} { line := "wat", cursor := 3 }
    assertEq unique.line "watch "
    let middle := Shell.complete {} { line := "wat demo", cursor := 2 }
    assertEq middle.line "watch demo"
    assertEq middle.cursor 5⟩,
  ⟨"console.shell.quoted-file-completion", do
    let line := "run squares/v1 --input \"data/n"
    let part := Completion.context line line.length
    assertEq part.fragment "data/n"
    assertEq part.before #["run", "squares/v1", "--input"]
    let (completed, _) := Completion.apply line part ⟨"data/numbers with spaces.json", ""⟩
    assertEq (words completed).toOption (some ["run", "squares/v1", "--input", "data/numbers with spaces.json"])
    let world : ConsoleModel.World := { directories := #["/work", "/work/data", "/work/data/nested"] }
    let world := world.save "/work/data/numbers.json" "[]"
    let (result, _) := ConsoleModel.run (Completion.refreshFiles ⟨"/work", "test"⟩ {} line line.length) world
    let catalog ← unwrap result
    assertEq (Completion.candidates catalog part |>.map (·.value)) #["data/nested/", "data/numbers.json"]
    let directory := Shell.complete { files := #[⟨"data/", "Directory"⟩] }
      { line := "run squares/v1 --input da", cursor := 24 }
    assertTrue (directory.line.endsWith "data/" && directory.cycle.isNone) "Directory completion did not permit descent"⟩,
  ⟨"console.shell.edit-and-history", do
    assertEq (Shell.edit {} { line := "hellp", cursor := 3 } .delete).line "help"
    let state := Shell.edit {} { line := "hlp", cursor := 1 } (.text "e")
    assertEq state.line "help"
    assertEq state.cursor 2
    assertEq (Shell.edit {} state .backspace).line "hlp"
    let recalled := Shell.edit {} { line := "draft", cursor := 5, history := #["ps", "top"] } .up
    assertEq recalled.line "top"
    assertEq (Shell.edit {} recalled .up).line "ps"
    assertEq (Shell.edit {} recalled .down).line "draft"
    assertEq (Shell.edit {} recalled .clear).line ""⟩,
  ⟨"console.shell.anchored-frame", do
    let state : Shell.State := { line := "watch demo", cursor := 10 }
    for (width, height) in [(120, 35), (80, 24), (40, 12), (12, 6), (5, 3)] do
      let view := Shell.frame "test" {} state width height
      assertEq view.lines.size height
      assertEq view.promptRow (if height ≥ 5 then height - 2 else 2)
      assertTrue (view.lines.all (·.length < width)) "Frame exceeded terminal width"
      assertTrue (view.cursorColumn < width && view.cursorColumn > 0) "Cursor outside prompt"
    let view := Shell.frame "test" {} {} 80 24
    assertTrue (view.lines[21]!.startsWith "cloud>") "Prompt not at bottom"
    assertTrue (view.lines[22]!.contains '[') "Suggestions are not beneath prompt"
    assertEq (Shell.edit {} state .pageUp).line state.line⟩,
  ⟨"console.shell.retains-complete-copyable-transcript", do
    let ctx : Context := ⟨"/work", "test"⟩
    let lines := (Array.range 2100).map fun i => s!"record-{i}\n"
    let long := String.ofList (List.replicate 5000 'x') ++ "END-LONG-LINE\n"
    let program : Cli (Context × Bool) := do
      request (.write (String.join lines.toList))
      request (.write long)
      request (.write "partial")
      request (.write "-line\n")
      printStyled (Styled.text "colored-output" .green)
      return (ctx, true)
    let (result, world) := ConsoleModel.run (Shell.execute ctx {} {} program)
      { envs := #[("NO_COLOR", "1")] }
    let (outcome, state) ← unwrap result
    discard <| unwrap outcome
    assertEq state.transcript.plain (String.join lines.toList ++ long ++ "partial-line\ncolored-output\n")
    let (copied, world) := ConsoleModel.run (do
      let selected ← Shell.handleKey {} state .selectAll (80, 24)
      Shell.handleKey {} selected .interrupt (80, 24)) world
    discard <| unwrap copied
    assertEq world.clipboard state.transcript.plain⟩,
  ⟨"console.shell.wheel-pins-footer-and-pauses-follow", do
    let transcript := ({} : Shell.Transcript).append
      (String.join ((List.range 100).map fun i => s!"line-{i}\n"))
    let state : Shell.State := { transcript, line := "watch demo", cursor := 5 }
    let before := Shell.frame "test" {} state 80 24
    let (result, _) := ConsoleModel.run (Shell.handleKey {} state (.mouse ⟨64, 20, 8, false⟩) (80, 24))
    let scrolled ← unwrap result
    let after := Shell.frame "test" {} scrolled 80 24
    assertEq (after.lines.extract 20 24) (before.lines.extract 20 24 |>.set! 0 after.lines[20]!)
    assertEq after.promptRow before.promptRow
    assertEq after.cursorColumn before.cursorColumn
    assertEq scrolled.line state.line
    assertEq (scrolled.transcript.visibleStart 20) 78
    let streaming := { scrolled with transcript := scrolled.transcript.append "new log\n" }
    assertEq ((Shell.frame "test" {} streaming 80 24).lines.extract 0 20) (after.lines.extract 0 20)
    let (result, _) := ConsoleModel.run (Shell.handleKey {} streaming (.mouse ⟨65, 20, 8, false⟩) (80, 24))
    let resumed ← unwrap result
    assertEq (resumed.transcript.visibleStart 20) 81
    let (result, _) := ConsoleModel.run (Shell.handleKey {} resumed (.mouse ⟨0, 10, 21, false⟩) (80, 24))
    assertTrue (← unwrap result).transcript.top.isNone "Clicking the footer did not resume follow"⟩,
  ⟨"console.shell.drag-copy-and-resize", do
    let transcript := ({} : Shell.Transcript).append "hello world\nsecond line\n"
    let action : Cli Shell.State := do
      let state ← Shell.handleKey {} { transcript } (.mouse ⟨0, 2, 1, false⟩) (80, 24)
      let state ← Shell.handleKey {} state (.mouse ⟨32, 6, 2, false⟩) (80, 24)
      Shell.handleKey {} state (.mouse ⟨0, 6, 2, true⟩) (80, 24)
    let (result, world) := ConsoleModel.run action
    let state ← unwrap result
    assertEq world.clipboard "ello world\nsecon"
    assertEq (world.trace.filter (· == "copyClipboard")).size 1
    assertEq (state.transcript.resize 5).selectedText world.clipboard
    let (result, _) := ConsoleModel.run (Shell.handleKey {} state .escape (80, 24))
    assertTrue (← unwrap result).transcript.selection.isNone "Escape did not clear selection"⟩,
  ⟨"console.shell.wrap-copy-unicode-and-anchor", do
    let transcript := (({} : Shell.Transcript).resize 8).append "λ 日本語 🙂\nabcdefghijklmnopqrstuvwxyz\nend"
    assertTrue (transcript.rows.all fun row =>
      (Styled.plain row.text).toList.foldl (fun n c => n + Shell.Transcript.cellWidth c) 0 ≤ 8)
      "Wide characters escaped the pane"
    assertEq transcript.selectAll.selectedText "λ 日本語 🙂\nabcdefghijklmnopqrstuvwxyz\nend"
    let anchored := { transcript with top := some 3 }
    let resized := anchored.resize 5
    let origin := resized.rows[resized.top.getD 0]!.origin
    assertEq origin.line transcript.rows[3]!.origin.line
    assertTrue (origin.column ≤ transcript.rows[3]!.origin.column) "Resize lost the reading position"⟩,
  ⟨"console.shell.copy-failure-keeps-session", do
    let state : Shell.State := { transcript := (({} : Shell.Transcript).append "copy me").selectAll }
    let (result, world) := ConsoleModel.run (Shell.handleKey {} state .interrupt (80, 24)) { failAt := some 0 }
    let state ← unwrap result
    assertTrue (state.notice.startsWith "Could not copy:") "Copy failure was silent"
    assertTrue world.clipboard.isEmpty "Failed copy changed the clipboard"⟩,
  ⟨"console.shell.key-decoding", do
    for (bytes, expected) in [(keyBytes "\x1b[A", Input.Key.up), (keyBytes "\x1b[Z", .backTab),
        (keyBytes "\x1b[3~", .delete), (keyBytes "λ", .text "λ"), ([4], .eof)] do
      let (result, world) := ConsoleModel.run Input.read { keys := bytes }
      assertEq (← unwrap result) expected
      assertTrue world.keys.isEmpty "Key sequence not consumed"
    let (result, _) := ConsoleModel.run Input.read { keys := keyBytes "\x1b[200~help\nquit λ\x1b[201~" }
    assertEq (← unwrap result) (.text "help quit λ")⟩,
  ⟨"console.shell.mouse-decoding", do
    for (bytes, expected) in [
        (keyBytes "\x1b[<64;20;8M", Input.Key.mouse ⟨64, 20, 8, false⟩),
        (keyBytes "\x1b[<65;120000;80000M", .mouse ⟨65, 120000, 80000, false⟩),
        (keyBytes "\x1b[<32;6;2M", .mouse ⟨32, 6, 2, false⟩),
        (keyBytes "\x1b[<0;6;2m", .mouse ⟨0, 6, 2, true⟩),
        (keyBytes "\x1b[M`4(", .mouse ⟨64, 20, 8, false⟩),
        (keyBytes "\x1b[<64;0;2M", .idle), (keyBytes "\x1b[1;5F", .scrollBottom)] do
      let (result, world) := ConsoleModel.run Input.read { keys := bytes ++ keyBytes "x" }
      assertEq (← unwrap result) expected
      assertEq world.keys (keyBytes "x") "Mouse payload leaked into the command line"⟩
]

end LeanCloudTests
