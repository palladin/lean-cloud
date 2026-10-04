import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open LeanCloudCli

private def keyBytes (text : String) : List UInt32 := text.toUTF8.data.toList.map (·.toUInt32)

private def suggestions (line : String) : Array String :=
  (Completion.candidates { programs := #[⟨"squares/v1", "Squares"⟩], runs := #[⟨"demo", "squares/v1"⟩] }
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
  ⟨"console.shell.verbose-completion", do
    for line in ["deploy --", "deploy my_app --"] do
      assertEq (suggestions line) #["--workers", "--verbose", "--help"]
    assertEq (suggestions "up --") #["--verbose", "--help"]
    assertEq (suggestions "deploy -v") #["-v"]
    for line in ["deploy -v ", "deploy --verbose my_app "] do
      assertEq (suggestions line) #["--workers"]
    assertEq (suggestions "deploy --workers ") #[]
    assertEq (suggestions "up --verbose ") #[]⟩,
  ⟨"console.shell.completion-cycles", do
    let start : Shell.State := { line := "r", cursor := 1 }
    let first := Shell.complete {} start
    let second := Shell.complete {} first
    assertEq first.line "run"
    assertEq second.line "result"
    assertEq (Shell.complete {} second true).line "run"
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
    let recalled := Shell.edit {} { line := "draft", cursor := 5, history := #["ps", "nodes"] } .up
    assertEq recalled.line "nodes"
    assertEq (Shell.edit {} recalled .up).line "ps"
    assertEq (Shell.edit {} recalled .down).line "draft"
    assertEq (Shell.edit {} recalled .clear).line ""⟩,
  ⟨"console.shell.anchored-frame", do
    let transcript := (Array.range 70).map (fun i => Styled.text s!"Output {i}")
    let state : Shell.State := { line := "watch demo", cursor := 10, transcript }
    for (width, height) in [(120, 35), (80, 24), (40, 12), (12, 6), (5, 3)] do
      let view := Shell.frame "test" {} state width height
      assertEq view.lines.size height
      assertEq view.promptRow (height - 2)
      assertTrue (view.lines.all (·.length < width)) "Frame exceeded terminal width"
      assertTrue (view.cursorColumn < width && view.cursorColumn > 0) "Cursor outside prompt"
    let view := Shell.frame "test" {} {} 80 24
    assertTrue (view.lines[21]!.startsWith "cloud>") "Prompt not at bottom"
    assertTrue (view.lines[22]!.contains '[') "Suggestions are not beneath prompt"
    let scrolled := Shell.frame "test" {} (Shell.edit {} state .pageUp) 80 24
    assertTrue (!(scrolled.lines.any (· == "Output 69"))) "Output scroll ignored"⟩,
  ⟨"console.shell.key-decoding", do
    for (bytes, expected) in [(keyBytes "\x1b[A", Input.Key.up), (keyBytes "\x1b[Z", .backTab),
        (keyBytes "\x1b[3~", .delete), (keyBytes "λ", .text "λ"), ([4], .eof)] do
      let (result, world) := ConsoleModel.run Input.read { keys := bytes }
      assertEq (← unwrap result) expected
      assertTrue world.keys.isEmpty "Key sequence not consumed"
    let (result, _) := ConsoleModel.run Input.read { keys := keyBytes "\x1b[200~help\nquit λ\x1b[201~" }
    assertEq (← unwrap result) (.text "help quit λ")⟩
]

end LeanCloudTests
