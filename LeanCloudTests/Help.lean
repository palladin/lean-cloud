import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open LeanCloudCli

private def ctx : Context := ⟨"/work", "test"⟩
private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1
private def suggestions (line : String) : Array String :=
  (Completion.candidates {} (Completion.context line line.length)).map (·.value)

def helpCases : Array TestCase := #[
  ⟨"console.help.removed-command-is-not-advertised", do
    assertTrue (Help.find? "nodes").isNone "Obsolete nodes command is still advertised"
    assertEq (suggestions "nod") #[]
    let (result, world) := ConsoleModel.run (command ctx ["nodes"]) {}
    assertTrue result.toOption.isNone "Removed nodes command still executes"
    assertTrue world.trace.isEmpty "Unknown command performed host operations"
    for topic in ["status", "top", "inspect", "watch"] do
      assertTrue (Help.find? topic).isSome s!"Missing supported inspection command: {topic}"⟩,
  ⟨"console.help.every-command-and-alias-is-read-only", do
    for topic in Help.commands do
      let mut canonical := none
      for name in #[topic.name] ++ topic.aliases do
        for args in [["help", name], [name, "--help"], [name, "-h"]] do
          let (result, world) := ConsoleModel.run (dispatch ctx args)
          let (selected, keepGoing) ← unwrap result
          assertTrue (keepGoing && selected.root == ctx.root && selected.project == ctx.project)
            s!"Help changed context or exited: {args}"
          assertTrue (world.trace.all (· == "write")) s!"Help performed host actions: {args}"
          assertTrue (has world.stdout s!"Usage: {topic.usage}" && has world.stdout "Options:" &&
            has world.stdout "Examples:") s!"Incomplete command help: {name}"
          for (option, _) in topic.options do assertTrue (has world.stdout option) s!"Missing option: {option}"
          if let some text := canonical then assertEq world.stdout text "Help forms disagree"
          canonical := some world.stdout⟩,
  ⟨"console.help.flags-before-or-after-arguments-never-execute", do
    for args in [["init", "my-app", "--help"], ["open", "--help", "my-app"],
      ["use", "--help", "deployment"], ["deploy", "app", "-v", "--help"],
      ["run", "demo", "--input", "missing.json", "--help"], ["kill", "one", "-h"],
      ["pause", "--help", "one"], ["watch", "one", "--help"], ["top", "--once", "--help"]] do
      let (result, world) := ConsoleModel.run (dispatch ctx args)
      let (_, keepGoing) ← unwrap result
      assertTrue keepGoing "Help exited the console"
      assertTrue (world.trace.all (· == "write")) s!"Help executed the command: {args}"⟩,
  ⟨"console.help.one-shot-ignores-invalid-configuration", do
    let initial := ({ env := some "INVALID", directories := #[] } : ConsoleModel.World)
      |>.save "/work/lean-cloud.json" "broken"
      |>.save "/home/test/.local/state/lean-cloud/deployments.json" "broken"
    for args in [["help"], ["--help"], ["-h"], ["help", "deploy"], ["top", "--help"]] do
      let (result, world) := ConsoleModel.run (application args) initial
      assertEq (← unwrap result) 0
      assertTrue (world.trace.all (· == "write") && world.stderr.isEmpty) "Help required application setup"
      assertEq world.files initial.files⟩,
  ⟨"console.help.unknown-topic-and-invalid-usage", do
    for args in [["help", "unknown"], ["unknown", "--help"], ["help", "deploy", "extra"]] do
      let (result, world) := ConsoleModel.run (application args)
      assertEq (← unwrap result) 1
      assertTrue (has world.stderr "Unknown command" || has world.stderr "Usage: help") "No useful help error"
      assertTrue (world.trace.all (· == "write")) "Invalid help had host side effects"⟩,
  ⟨"console.help.completion-is-contextual", do
    assertEq (suggestions "help wa") #["watch"]
    assertEq (suggestions "help ex") #["exit"]
    assertEq (suggestions "deploy --h") #["--help"]
    assertEq (suggestions "kill -h") #["-h"]
    assertEq (suggestions "run --h") #["--help"]
    assertEq (suggestions "unknown --h") #[]
    for line in ["run demo --input --h", "run demo --id --h", "init app --sdk --h", "deploy --help --h"] do
      assertEq (suggestions line) #[] "Suggested a flag as an argument value or repeated help"⟩,
  ⟨"console.help.live-view-help-stays-in-transcript", do
    let input := "watch --help\rtop -h\rhelp deploy\rquit --help\rquit\r"
    let (result, world) := ConsoleModel.run (application [])
      { keys := input.toUTF8.data.toList.map (·.toUInt32) }
    assertEq (← unwrap result) 0
    assertTrue (world.keys.isEmpty && world.processes.isEmpty && !world.terminal) "Help ran a command or lost input"
    assertEq (world.trace.filter (· == "enterTerminal")).size 1 "Help opened a fullscreen view"
    assertEq (world.trace.filter (· == "leaveTerminal")).size 1
    for usage in ["Usage: watch RUN", "Usage: top", "Usage: deploy", "Usage: quit"] do
      assertTrue (has world.stdout usage) s!"Missing help in transcript: {usage}"⟩
]

end LeanCloudTests
