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
    let points : Array ResourceSample := #[
      { incarnation := "boot", timeNs := 1000000000, cpuNs := some 0 },
      { incarnation := "boot", timeNs := 2000000000, cpuNs := some 2500000000,
        cpuCapacityMillis := some 1000,
        memory := some 1048576, memoryLimit := some 2097152,
        diskUsed := some 1048576, diskCapacity := some 2097152 }]
    let lines := (SnapshotMetrics.lines points 56).map Styled.plain
    assertTrue (lines.any (fun line => has line "250.00%" && has line "+")) "CPU was silently capped at one core"
    assertTrue (lines.any (fun line => has line "1.0 MiB / 2.0 MiB")) "Memory capacity missing"
    assertTrue (lines.any (fun line => has line "Disk")) "Filesystem scope missing"
    assertTrue (lines.any (fun line => has line "Net RX" && has line "unavailable")) "First counter sample became a false zero rate"⟩,
  ⟨"console.style.live-frame-resizes", do
    let ctx : Context := ⟨"/work", "test"⟩
    let run : Run := ⟨"one", "image", ⟨"demo/v1", "unit", "nat", "", none,
      #[⟨"Demo.lean", "cloud {\n  return 42\n}", #[]⟩]⟩, Json.null⟩
    let node : Node := { name := ctx.node "worker1", state := "running" }
    let resources : Array ResourceSample := #[{ incarnation := "boot", timeNs := 1000, memory := some 1048576 }]
    for width in [5, 40, 80, 120, 180] do
      for height in [12, 24, 35] do
        let plain := Watch.frame ctx run #[] #[{ name := node.name, resources }] {} width height
        let colored := Watch.frame ctx run #[] #[{ name := node.name, resources }] {} width height "" true
        assertEq (colored.map uncolor) plain
        assertTrue (plain.size < height && plain.all (·.length ≤ width)) "Resource frame escaped terminal dimensions"⟩,
  ⟨"console.style.host-and-container-capacity", do
    let before : ResourceSample := { incarnation := "boot", timeNs := 1000000000, cpuNs := some 0 }
    let after : ResourceSample := {
      incarnation := "boot", timeNs := 2000000000, cpuNs := some 1000000000,
      nodeName := some "aks-node-1", hostname := some "worker1-0", cpuCores := some 8,
      memoryCapacity := some 17179869184, cpuCapacityMillis := some 1500,
      memory := some 1048576, memoryLimit := some 536870912 }
    let lines := (SnapshotMetrics.lines #[before, after] 80).map Styled.plain
    assertEq lines.size 9
    assertEq lines[0]! "Node aks-node-1"
    assertEq lines[1]! "Host 8 logical CPUs · 16.0 GiB RAM"
    assertTrue (has lines[2]! "100.00% / 1.500 CPUs" && !has lines[2]! "+")
      "CPU meter did not use fractional container capacity"
    assertTrue (has lines[3]! "1.0 MiB / 512.0 MiB") "Host RAM replaced container limit"
    let unknown := (SnapshotMetrics.lines #[before, { after with cpuCapacityMillis := none }] 80).map Styled.plain
    assertTrue (has unknown[2]! "100.00%" && !has unknown[2]! "[") "Missing CPU capacity fabricated a meter"
    let fallback := (SnapshotMetrics.lines #[{ after with nodeName := none }] 80).map Styled.plain
    assertEq fallback[0]! "Container worker1-0"
    let missing := (SnapshotMetrics.lines #[before] 80).map Styled.plain
    assertEq missing[0]! "Container unavailable"
    assertTrue (has missing[1]! "unavailable" && !has missing[1]! "0 logical CPUs")
      "Missing host capacity became zero"⟩,
  ⟨"console.style.shared-theme-and-no-color", do
    let ctx : Context := ⟨"/work", "test"⟩
    let program : Cli (Context × Bool) := do
      printHeading "RUN    STATUS"
      printStyled (Styled.text "one    " .cyan ++ Styled.text "running" .green)
      return (ctx, true)
    let (result, world) := ConsoleModel.run (Shell.execute ctx {} {} program) {}
    discard <| unwrap result
    assertTrue (has world.stdout "\x1b[0;30;46mRUN") "Table header lost its theme in the shell"
    assertTrue (has world.stdout "\x1b[0;32mrunning") "Status lost its theme in the shell"
    for envs in [#[("NO_COLOR", "1")], #[("TERM", "dumb")]] do
      let (result, world) := ConsoleModel.run (Shell.execute ctx {} {} program) { envs }
      discard <| unwrap result
      assertTrue (!has world.stdout "\x1b[0;30;46m" && !has world.stdout "\x1b[0;32m") "Color opt-out was ignored"⟩
]

end LeanCloudTests
