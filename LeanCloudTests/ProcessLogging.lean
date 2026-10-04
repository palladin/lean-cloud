import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open LeanCloudCli

private def log : System.FilePath := "/work/build.log"
private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1
private def chunks : List ProcessChunk :=
  [{ stdout := "first\n".toUTF8 }, { stderr := "warning\n".toUTF8 },
   { stdout := "last".toUTF8, exitCode := some 0 }]
private def initial : ConsoleModel.World := { stream := some (fun _ => .ok chunks), keys := [0, 0] }
private def ctx : Context := ⟨"/work", "test"⟩

private def program (verbose := false) : Cli (Context × Bool) := do
  withLock "/work/deploy.lock" do
    Process.runLogged "build" #[] log verbose
    return (ctx, true)

def processLoggingCases : Array TestCase := #[
  ⟨"console.logging.quiet-and-verbose-save-identical-output", do
    for verbose in [false, true] do
      let (result, world) := ConsoleModel.run (program verbose) initial
      discard (unwrap result)
      assertEq (world.file log) (some "first\nwarning\nlast")
      assertEq world.stdout (if verbose then "first\nlast\n" else "")
      assertEq world.stderr (if verbose then "warning\n" else "")
      assertTrue (world.children.isEmpty && world.locks.isEmpty) "Logging leaked resources"
      assertEq (world.trace.filter (· == "writeFile")).size 1
      assertEq (world.trace.filter (· == "appendFile")).size 3
      assertTrue (!world.trace.contains "readFile") "Log was reread to collect a tail"
      assertTrue (world.trace.toList.idxOf "appendFile" < world.trace.toList.idxOf "closeProcess")
        "Log was written only after process exit"⟩,
  ⟨"console.logging.split-utf8-and-crlf", do
    let text := "λ🙂\r\nfinal"
    let parts := text.toUTF8.data.toList.map fun byte => { stdout := ByteArray.mk #[byte] : ProcessChunk }
    let (result, world) := ConsoleModel.run (program) { initial with
      stream := some (fun _ => .ok (parts ++ [{ exitCode := some 0 }])) }
    discard (unwrap result)
    assertEq (world.file log) (some "λ🙂\nfinal")⟩,
  ⟨"console.logging.failure-tail-is-bounded-log-is-complete", do
    let lines := (Array.range 100).map (fun i => s!"line-{i}\n")
    let long := String.ofList (List.replicate 40000 'x') ++ "final error"
    let parts := lines.toList.map (fun line => { stdout := line.toUTF8 : ProcessChunk })
    let (result, world) := ConsoleModel.run (program) { initial with stream := some (fun _ =>
      .ok (parts ++ [{ stderr := long.toUTF8, exitCode := some 7 }])) }
    let .error error := result | throw (IO.userError "Failed build was accepted")
    assertTrue (has error "code 7" && has error log.toString) "No exit code/log path"
    assertEq (world.file log) (some (String.join lines.toList ++ long))
    assertTrue (has world.stderr "line-81\n" && !has world.stderr "line-80\n" &&
      has world.stderr "final error") "Tail does not contain the last 20 lines"
    assertTrue (world.stderr.length < 22000) "Error display retained an unbounded line"
    assertTrue (world.children.isEmpty && world.locks.isEmpty) "Failed build leaked resources"⟩,
  ⟨"console.logging.verbose-failure-does-not-repeat-output", do
    let (result, world) := ConsoleModel.run (program true) { initial with
      stream := some (fun _ => .ok [{ stderr := "bad build\n".toUTF8, exitCode := some 9 }]) }
    let .error error := result | throw (IO.userError "Failed build was accepted")
    assertEq world.stderr "bad build\n"
    assertEq (world.file log) (some "bad build\n")
    assertTrue (has error "code 9" && has error log.toString) "Verbose failure lost log path"⟩,
  ⟨"console.logging.quiet-shell-still-edits-and-resizes", do
    let (result, world) := ConsoleModel.run (Shell.execute ctx {} {} (program))
      { initial with keys := [104, 101], sizes := [(80, 24), (50, 12)] }
    let (result, state) ← unwrap result
    discard (unwrap result)
    assertEq state.line "he"
    assertTrue state.transcript.isEmpty "Quiet output reached the transcript"
    assertTrue (has world.stdout "\x1b[22;" && has world.stdout "\x1b[10;") "Quiet mode ignored resize"
    assertEq (world.file log) (some "first\nwarning\nlast")⟩,
  ⟨"console.logging.interrupt-keeps-log-and-releases-resources", do
    for verbose in [false, true] do
      let (result, world) := ConsoleModel.run (Shell.execute ctx {} {} (program verbose))
        { initial with keys := [0, 3] }
      let (result, _) ← unwrap result
      let .error error := result | throw (IO.userError "Interrupt ignored")
      assertTrue (has error "interrupted" && has error log.toString) "No interruption/log explanation"
      assertEq (world.file log) (some "first\n")
      assertTrue (world.children.isEmpty && world.locks.isEmpty) "Interrupt leaked resources"⟩,
  ⟨"console.logging.host-failure-cleanup", do
    for verbose in [false, true] do
      let (_, success) := ConsoleModel.run (program verbose) initial
      for index in [:success.trace.size] do
        if ["closeProcess", "unlock"].contains success.trace[index]! then continue
        let (result, world) := ConsoleModel.run (program verbose) { initial with failAt := some index }
        assertTrue result.toOption.isNone s!"Host failure swallowed at {index}"
        assertTrue (world.children.isEmpty && world.locks.isEmpty) s!"Resource leak at {index}"
        if success.trace[index]! == "writeFile" then
          assertTrue world.processes.isEmpty "Started work without a writable log"
        if success.trace[index]! == "appendFile" then
          let .error error := result | throw (IO.userError "Log write failure swallowed")
          assertTrue (has error "may be partial" && has error log.toString) "No log failure context"⟩,
  ⟨"console.logging.invalid-flags-have-no-effects", do
    for args in [["deploy", "--bad"], ["deploy", "a", "b"], ["deploy", "-v", "--verbose"],
      ["up", "app"], ["up", "-v", "-v"], ["up", "--verbose", "--bad"]] do
      let (result, world) := ConsoleModel.run (command ctx args) initial
      assertTrue result.toOption.isNone s!"Invalid flags accepted: {args}"
      assertTrue world.trace.isEmpty "Invalid flags caused host effects"⟩
]

end LeanCloudTests
