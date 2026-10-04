import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open LeanCloudCli

private def bytes (text : String) : List UInt32 := text.toUTF8.data.toList.map (·.toUInt32)
private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1
private def ctx : Context := ⟨"/work", "stream-test"⟩

private def chunks : List ProcessChunk :=
  [{ stdout := "first\n".toUTF8 }, { stderr := "warning\n".toUTF8 },
   { stdout := "last".toUTF8, exitCode := some 0 }]

private def program : Cli (Context × Bool) := do
  withLock "/work/deploy.lock" do
    let code ← Process.stream "test-build" #[]
    unless code == 0 do throw s!"Failed: {code}"
    return (ctx, true)

private def initial : ConsoleModel.World := { stream := some (fun _ => .ok chunks) }

def streamingCases : Array TestCase := #[
  ⟨"console.stream.decode-boundaries", do
    let original := "aλ🙂漢字\r\nb\rc\n"
    let encoded := original.toUTF8
    for size in [1:encoded.size + 1] do
      let mut decoder : Process.Decoder := {}
      let mut text := ""
      for i in [:((encoded.size + size - 1) / size)] do
        let (part, next) := Process.decode decoder (encoded.extract (i * size) ((i + 1) * size))
        text := text ++ part; decoder := next
        assertTrue (decoder.pending.size ≤ 3) "Decoder retained more than a UTF-8 prefix"
      let (last, finalDecoder) := Process.decode decoder ByteArray.empty true
      assertEq (text ++ last) "aλ🙂漢字\nb\nc\n"
      assertTrue finalDecoder.pending.isEmpty "Decoder left bytes after EOF"
    let (text, _) := Process.decode {} (ByteArray.mk #[0xFF, 0xC2]) true
    assertEq text "��"
    let (text, _) := Process.decode {} "\x1b[2J\x07".toUTF8 true
    assertTrue (!text.contains '\x1b' && !text.contains '\x07') "Process output contains terminal controls"⟩,
  ⟨"console.stream.incremental-transcript", do
    let state := Shell.appendOutput {} "fir"
    assertEq state.partialLine "fir"
    assertTrue state.transcript.isEmpty "Partial output was prematurely split"
    let state := Shell.appendOutput state "st\nseco"
    assertEq state.transcript #["first"]
    assertEq state.partialLine "seco"
    let view := Shell.frame "test" {} state 80 24 true
    assertTrue (view.lines.any (· == "seco")) "Partial line is not visible"
    let long := Shell.appendOutput {} (String.ofList (List.replicate 20000 'x'))
    assertTrue (long.partialLine.length ≤ 4096 && long.transcript.all (·.length ≤ 4096)) "Unbounded partial line"
    let old : Shell.State := { transcript := (Array.range 100).map toString, scroll := 20 }
    let updated := Shell.appendOutput old "new\n"
    assertEq updated.scroll 21 "Live output reset the scroll position"⟩,
  ⟨"console.stream.plain-output", do
    let (result, world) := ConsoleModel.run (Process.stream "test-build" #[]) initial
    assertEq (← unwrap result) 0
    assertEq world.stdout "first\nlast\n"
    assertEq world.stderr "warning\n"
    assertTrue (world.children.isEmpty && !world.trace.contains "key") "Plain output read terminal keys or leaked process"
    let firstWrite := world.trace.toList.idxOf "write"
    let close := world.trace.toList.idxOf "closeProcess"
    assertTrue (firstWrite < close) "Output appeared only after process cleanup"⟩,
  ⟨"console.stream.busy-edit-and-resize", do
    let initial := { initial with keys := bytes "he", sizes := [(80, 24), (50, 12)] }
    let (result, world) := ConsoleModel.run (Shell.execute ctx {} {} program) initial
    let (result, state) ← unwrap result
    discard (unwrap result)
    assertEq state.line "he" "Draft typing was lost while command ran"
    assertEq state.transcript #["first", "warning", "last"]
    assertTrue (has world.stdout "\x1b[22;" && has world.stdout "\x1b[10;") "Busy prompt ignored resize"
    assertTrue (world.children.isEmpty && world.locks.isEmpty) "Completed command leaked resources"⟩,
  ⟨"console.stream.busy-scroll", do
    let state : Shell.State := { transcript := (Array.range 100).map (fun i => s!"line {i}") }
    let (result, _) := ConsoleModel.run (Shell.execute ctx {} state program)
      { initial with keys := bytes "\x1b[5~" ++ [0] }
    let (_, state) ← unwrap result
    assertTrue (state.scroll > 0) "PgUp was ignored or reset by new output"⟩,
  ⟨"console.stream.idle-does-not-redraw", do
    let quiet := some fun _ => .ok ([{}, {}, {}, {}, { exitCode := some 0 }] : List ProcessChunk)
    let (result, world) := ConsoleModel.run (Shell.execute ctx {} {} program)
      { initial with stream := quiet, keys := [0, 0, 0, 0] }
    let (result, _) ← unwrap result
    discard (unwrap result)
    assertEq (world.trace.filter (· == "pollProcess")).size 5
    -- One initial busy frame and one final newline, not a frame on every idle poll.
    assertEq (world.trace.filter (· == "write")).size 2⟩,
  ⟨"console.stream.interrupt-unwinds-command", do
    let (result, world) := ConsoleModel.run (Shell.execute ctx {} {} program) { initial with keys := [3] }
    let (result, _) ← unwrap result
    assertTrue result.toOption.isNone "Interrupt was ignored"
    assertTrue (world.children.isEmpty && world.locks.isEmpty) "Interrupt bypassed finalizers"
    assertEq (world.trace.filter (· == "pollProcess")).size 1
    assertTrue (world.processes.all (·.command == "test-build")) "Interrupt changed deployment services"⟩,
  ⟨"console.stream.exit-failure", do
    let scripted := some fun _ => .ok [{ stderr := "bad build\n".toUTF8, exitCode := some 7 : ProcessChunk }]
    let (result, world) := ConsoleModel.run program { initial with stream := scripted }
    assertTrue result.toOption.isNone "Nonzero exit accepted"
    assertTrue (world.children.isEmpty && world.locks.isEmpty) "Failed process leaked resources"
    assertEq world.stderr "bad build\n"⟩,
  ⟨"console.stream.failure-cleanup", do
    let (_, successful) := ConsoleModel.run (Shell.execute ctx {} {} program) { initial with keys := [0, 0] }
    for index in [:successful.trace.size] do
      if ["closeProcess", "unlock"].contains successful.trace[index]! then continue
      let (_, world) := ConsoleModel.run (Shell.execute ctx {} {} program)
        { initial with keys := [0, 0], failAt := some index }
      assertTrue (world.children.isEmpty && world.locks.isEmpty)
        s!"Resources leaked at {index}: {successful.trace[index]!}"⟩
]

end LeanCloudTests
