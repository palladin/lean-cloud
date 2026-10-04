import LeanCloudTests.Support
import LeanCloudCli.Console
import LeanCloud.Source

namespace LeanCloudTests
open Lean LeanCloud LeanCloudCli

private def basicSample (time : Nat) (session := "boot-1") (rx := 0) : Sample :=
  ⟨time, session, 12500, 1048576, 2097152, rx, 0, 0, 0⟩

def consoleCases : Array TestCase := #[
  ⟨"console.quoted-input", do
    assertEq (words "run logs --input 'files with spaces.json' --id \"example-1\"").toOption
      (some ["run", "logs", "--input", "files with spaces.json", "--id", "example-1"])
    assertEq (words "run logs --input files\\ with\\ spaces.json").toOption
      (some ["run", "logs", "--input", "files with spaces.json"])⟩,
  ⟨"console.literal-shell-text", do
    assertEq (words "logs '$(touch file);`command`'").toOption (some ["logs", "$(touch file);`command`"])
    assertTrue (words "run 'unfinished").toOption.isNone "Unclosed quote accepted"⟩,
  ⟨"console.run-id-isolation", do
    for value in ["../other", "", "a/b", "x\nworker", "run:1"] do
      assertTrue (!validId value) s!"Unsafe run id accepted: {reprStr value}"
    assertTrue (validId "run-42_abc") "Valid id rejected"
    let a : Context := ⟨"/work", "one"⟩
    let b : Context := ⟨"/work", "two"⟩
    assertTrue (a.directory "same" != b.directory "same") "Deployment catalogs overlap"⟩,
  ⟨"console.terminal-controls", do
    assertEq (safe "ok\x1b[2J\r\n\x7f") "ok [2J   "
    assertTrue (!(clip 8 "0123456789").contains '\x1b') "Unsafe clipping"⟩,
  ⟨"console.metric-units", do
    assertEq (bytes "1.5MiB") 1572864
    assertEq (bytes "1.5MB") 1500000
    assertEq (bytes "512 B") 512
    assertEq (decimal "12.34") 12340
    assertEq (percent 70) "0.07%"
    assertEq (percent 12340) "12.34%"
    assertEq (percent 120) "0.12%"⟩,
  ⟨"console.counter-restarts", do
    assertEq (rate (basicSample 1000 "a" 100) (basicSample 3000 "a" 1100) (·.rx)) (some 500)
    assertEq (rate (basicSample 1000 "a" 100) (basicSample 3000 "b" 1100) (·.rx)) none
    assertEq (rate (basicSample 1000 "a" 100) (basicSample 3000 "a" 10) (·.rx)) none
    assertEq (rate (basicSample 1000) (basicSample 1000) (·.rx)) none⟩,
  ⟨"console.bounded-history", do
    let samples := (Array.range 80).map fun i => ("worker", basicSample i "a" i)
    let history := remember #[] samples
    assertEq history[0]!.points.size 30
    let restarted := remember history #[("worker", basicSample 90 "b")]
    assertEq restarted[0]!.points.size 1
    assertTrue (!(remember restarted #[])[0]!.fresh) "Missing sample reused as live data"⟩,
  ⟨"console.source-map-validation", do
    let source : ProgramSource := ⟨"Example.lean", "first\nCloud.exec body\nlast", #[]⟩
    let mapped ← unwrap (source.locate #[("work", "Cloud.exec")])
    assertEq mapped.sites[0]!.line 2
    assertTrue (source.locate #[("work", "missing")]).toOption.isNone "Missing source marker accepted"
    assertTrue (({ source with text := "same\nsame" }).locate #[("work", "same")]).toOption.isNone
      "Ambiguous source marker accepted"⟩,
  ⟨"console.execution-event-roundtrip", do
    let event : ExecutionEvent := ⟨"boot", 17, 42, "worker1", some 3, "0:1/0:2", "replay", "readBlob", "example"⟩
    let parsed := event? ("@lean-cloud " ++ (toJson event).compress)
    assertEq (parsed.map (·.location)) (some "0:1/0:2")
    assertTrue (event? "ordinary log line").isNone "Ordinary log interpreted as event"⟩,
  ⟨"console.frame-live-and-stopped", do
    let ctx : Context := ⟨"/work", "test"⟩
    let source : ProgramSource := ⟨"Example.lean", "cloud {\n  Cloud.exec work\n}", #[⟨"work", 2⟩]⟩
    let info : ProgramInfo := ⟨"example/v1", "unit/v1", "nat/v1", "", none, some source⟩
    let run : Run := ⟨"run-1", "image", info, Json.null⟩
    let event : ExecutionEvent := ⟨"boot", 1, 20, "worker1", some 2, "0:1", "execute", "work", "example"⟩
    let events := #[("worker1", #[event])]
    let node : Node := { name := ctx.node "worker1", state := "running", started := "boot", run := some run.id, role := "worker1" }
    let live := frame ctx run #[node] events #[] 0 0 120 30
    assertTrue (live.any (fun l => (l.splitOn "2   1").length > 1)) "Live source marker absent"
    let stopped := frame ctx run #[{ node with state := "exited" }] events #[] 0 0 120 30
    assertTrue (!(stopped.any (fun l => (l.splitOn "2   1").length > 1))) "Stopped process shown executing"
    for width in [40, 80, 120] do
      let lines := frame ctx run #[node] events #[] 0 0 width 24
      assertTrue (lines.size < 24 && lines.all (·.length ≤ width)) "Terminal frame exceeds dimensions"⟩
]
end LeanCloudTests
