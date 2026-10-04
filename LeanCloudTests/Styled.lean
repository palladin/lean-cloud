import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open Lean LeanCloud LeanCloudCli

private def uncolor (text : String) : String :=
  ["0", "0;2", "0;32", "0;33", "0;1;31", "0;36", "0;35", "0;34", "0;30;46", "0;1;37;44"].foldl
    (fun text code => text.replace ("\x1b[" ++ code ++ "m") "") text

private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1

def styledCases : Array TestCase := #[
  ⟨"console.style.clip-before-colors-and-sanitize", do
    let line := Styled.text "CPU " .cyan ++ Styled.text "||||" .green ++
      Styled.text " 25%" ++ Styled.text "\x1b[2J\nunsafe" .red
    for width in [:32] do
      let plain := Styled.render line width
      let colored := Styled.render line width true
      assertEq (uncolor colored) plain "Colors changed the visible layout"
      assertTrue (plain.length ≤ width && !plain.contains '\x1b' && !plain.contains '\n')
        "Style renderer allowed terminal control or exceeded width"
      assertTrue (colored.endsWith "\x1b[0m") "Color leaked into the next line"⟩,
  ⟨"console.style.wrapping-preserves-spans", do
    let line := Styled.text "abc" .cyan ++ Styled.text "DEFG" .red ++ Styled.text "hij"
    for start in [:12] do
      for stop in [start:13] do
        let slice := Styled.slice line start stop
        assertEq (Styled.plain slice) (String.ofList ("abcDEFGhij".toList.drop start |>.take (stop - start)))
    let part := Styled.slice line 2 6
    assertTrue ((Styled.render part 10 true).startsWith "\x1b[0;36mc\x1b[0;1;31mDEF")
      "Wrapping lost the original styles"⟩,
  ⟨"console.style.meters-and-rate-gaps", do
    assertEq (Styled.plain (meter 0 100 4)) "[····]"
    assertEq (Styled.plain (meter 25 100 4)) "[|···]"
    assertEq (Styled.plain (meter 100 100 4)) "[||||]"
    assertEq (Styled.plain (meter 250 100 4)) "[|||+]"
    assertEq (Styled.plain (meter 1 0 4)) "[unavailable]"
    assertEq (spark #[some 0, none, some 1, some 100] 4 (some 100)) "_·▁█"
    assertTrue (has (Styled.render (meter 75 100 4) 20 true) "\x1b[0;33m") "High usage lacks amber color"
    assertTrue (has (Styled.render (meter 95 100 4) 20 true) "\x1b[0;1;31m") "Full usage lacks red color"⟩,
  ⟨"console.style.filesystem-and-multicore-cpu", do
    let some disk := decodeFilesystem "/data" "Filesystem 1024-blocks Used Available Capacity Mounted\ndisk 2048 1024 1024 50% /\n"
      | throw (IO.userError "Filesystem could not be decoded")
    assertEq disk.used 1048576
    assertEq disk.capacity 2097152
    assertTrue (decodeFilesystem "/" "not a capacity").isNone "Malformed filesystem became zero usage"
    assertTrue (decodeFilesystem "/" "disk 0 0 0 0% /").isNone "Missing capacity became a valid meter"
    let current : Sample := ⟨1000, "boot", 250000, 1048576, 2097152, 0, 0, 0, 0⟩
    let lines := (metricLines #[current] 56 (some disk)).map Styled.plain
    assertTrue (lines.any (fun line => has line "250.00%" && has line "+")) "CPU was silently capped at one core"
    assertTrue (lines.any (fun line => has line "1.0 MiB / 2.0 MiB")) "Memory capacity missing"
    assertTrue (lines.any (fun line => has line "filesystem /data")) "Filesystem scope missing"
    assertTrue (lines.any (fun line => has line "Net RX" && has line "—")) "First counter sample became a false zero rate"⟩,
  ⟨"console.style.live-frame-resizes", do
    let ctx : Context := ⟨"/work", "test"⟩
    let run : Run := ⟨"one", "image", ⟨"demo/v1", "unit", "nat", "", none,
      some ⟨"Demo.lean", "cloud {\n  return 42\n}", #[]⟩⟩, Json.null⟩
    let node : Node := { name := ctx.container run "worker1", state := "running", started := "boot" }
    let points : Array Sample := #[⟨1000, "boot", 12000, 1048576, 2097152, 0, 0, 0, 0⟩,
      ⟨2000, "boot", 92000, 1048576, 2097152, 10000, 20000, 30000, 40000⟩]
    for width in [5, 40, 80, 120, 180] do
      for height in [12, 24, 35] do
        let plain := frame ctx run #[node] #[] #[⟨node.name, points, true⟩] 0 0 width height
        let colored := frame ctx run #[node] #[] #[⟨node.name, points, true⟩] 0 0 width height "" none true
        assertEq (colored.map uncolor) plain
        assertTrue (plain.size < height && plain.all (·.length ≤ width)) "Resource frame escaped terminal dimensions"⟩,
  ⟨"console.style.shared-theme-and-no-color", do
    let ctx : Context := ⟨"/work", "test"⟩
    let program : Cli (Context × Bool) := do
      printHeading "RUN    STATUS"
      printStyled (Styled.text "one    " .cyan ++ Styled.text "running" .green)
      return (ctx, true)
    let (result, _) := ConsoleModel.run (Shell.execute ctx {} {} program) {}
    let (_, state) ← unwrap result
    assertEq (state.transcript.map Styled.plain) #["RUN    STATUS", "one    running"]
    let view := Shell.frame "test" {} state 80 24 false true
    assertTrue (view.lines.any (fun line => has line "\x1b[0;30;46mRUN")) "Table header lost its theme in the shell"
    assertTrue (view.lines.any (fun line => has line "\x1b[0;32mrunning")) "Status lost its theme in the shell"
    for envs in [#[("NO_COLOR", "1")], #[("TERM", "dumb")]] do
      let (result, world) := ConsoleModel.run (Shell.execute ctx {} {} program) { envs }
      discard <| unwrap result
      assertTrue (!has world.stdout "\x1b[0;30;46m" && !has world.stdout "\x1b[0;32m") "Color opt-out was ignored"⟩
]

end LeanCloudTests
