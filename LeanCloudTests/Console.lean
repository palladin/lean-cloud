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
  ⟨"console.execution-event-roundtrip", do
    let event : ExecutionEvent := ⟨"boot", 17, 42, "worker1", some 3, "0:1/0:2", "replay", "readBlob", "example", none⟩
    let parsed := event? ("@lean-cloud " ++ (toJson event).compress)
    assertEq (parsed.map (·.location)) (some "0:1/0:2")
    assertTrue (event? "ordinary log line").isNone "Ordinary log interpreted as event"⟩,
  ⟨"console.watch-final-source", do
    let ctx : Context := ⟨"/work", "test"⟩
    let source : ProgramSource := ⟨"Example.lean", "cloud {\n  Cloud.exec work\n}", #[⟨"work", 2, 0, 2, 0⟩]⟩
    let info : ProgramInfo := ⟨"example/v1", "unit/v1", "nat/v1", "", none, #[source]⟩
    let run : Run := ⟨"run-1", "image", info, Json.null, defaultWorkerCount⟩
    let event : ExecutionEvent := ⟨"boot", 1, 20, "worker1", some 2, "0:1", "execute", "work", run.id, some "work"⟩
    let step : LeanCloudCli.Trace.Step := ⟨"2026-01-01T00:00:00.000000000Z", event, none, none, none⟩
    for status in ["completed", "paused", "cancelled", "result pending"] do
      let lines := Watch.frame ctx run #[step] #[] {} 120 35 status
      assertTrue (lines.any (fun l => (l.splitOn "2   > ").length > 1)) "Final source marker absent"
      assertTrue (lines.any (fun l => (l.splitOn status).length > 1)) "Run status absent"
      let label := if status == "result pending" then "No worker executing this branch" else "unavailable in last view"
      assertTrue (lines.any (fun l => (l.splitOn label).length > 1)) "Metric mode was not labeled"
    for width in [20, 40, 80, 120, 220] do
      for height in [8, 16, 24, 45] do
        let lines := Watch.frame ctx run #[step] #[] {} width height
        assertTrue (lines.size < height && lines.all (·.length < width)) "Watch exceeds terminal dimensions"⟩,
  ⟨"console.watch-live-navigation-has-no-timeline", do
    let nav : Watch.Navigation := {}
    for key in [Input.Key.text "[", .text "]", .end, .text "f"] do
      assertTrue (Watch.navigate #[] 1 nav key == nav) "Timeline navigation is still active"
    assertEq (Watch.navigate #[] 1 nav .pageDown 2).workers 1
    assertEq (Watch.navigate #[] 1 { workers := 2 } .pageDown 2).workers 2
    assertEq (Watch.navigate #[] 1 { workers := 2 } .pageUp 2).workers 1
    assertEq (Watch.navigate #[] 1 { workers := 3 } .home).workers 0⟩,
  ⟨"console.trace-order-and-dedup", do
    let event : ExecutionEvent := ⟨"old", 90, 9999, "worker1", some 2, "0:1", "execute", "work", "run", some "work"⟩
    let old : LeanCloudCli.Trace.Step := ⟨"2026-01-01T00:00:01.000000000Z", event, none, none, none⟩
    let new : LeanCloudCli.Trace.Step := ⟨"2026-01-01T00:00:02.000000000Z", { event with session := "new", seq := 0, elapsedMs := 0 }, none, none, none⟩
    let parsed := LeanCloudCli.Trace.parse (old.timestamp ++ " @lean-cloud " ++ (toJson event).compress)
    assertEq (parsed.map (·.id)) (some old.id)
    assertEq ((LeanCloudCli.Trace.merge #[new] #[old, new]).map (·.id)) #[old.id, new.id]
    assertTrue (LeanCloudCli.Trace.parse "ordinary output").isNone "Ordinary log became a step"⟩,
  ⟨"console.recorded-metric-rates-and-restarts", do
    let before : ResourceSample := {
      incarnation := "boot", timeNs := 1000000000,
      cpuNs := some 100000000, rx := some 100 }
    let after := { before with timeNs := 2000000000, cpuNs := some 600000000, rx := some 1100 }
    assertEq (SnapshotMetrics.rate before after (·.cpuNs) 100000) (some 50000)
    assertEq (SnapshotMetrics.rate before after (·.rx)) (some 1000)
    assertEq (SnapshotMetrics.rate before { after with incarnation := "restarted" } (·.cpuNs)) none
    assertEq (SnapshotMetrics.rate before { after with rx := some 0 } (·.rx)) none
    assertEq (SnapshotMetrics.rate before { after with rx := none } (·.rx)) none
    assertEq (SnapshotMetrics.rate before before (·.cpuNs)) none⟩,
  ⟨"console.watch-final-view-never-uses-live-stats", do
    let ctx : Context := ⟨"/work", "test"⟩
    let run : Run := ⟨"run", "image", ⟨"app/v1", "unit", "nat", "", none, #[]⟩, Json.null, 1⟩
    let step : Trace.Step := {
      timestamp := "1"
      event := ⟨"session", 1, 1, "worker1", some 0, "0:0", "execute", "", run.id, none⟩
      resources := some {
        incarnation := "boot", timeNs := 1000000000,
        memory := some 1048576, memoryLimit := some 4194304 } }
    let live : History := ⟨ctx.node "worker1", #[⟨10, "now", 999000, 9663676416, 99999999999, 0, 0, 0, 0⟩], true⟩
    let text := String.intercalate "\n" (Watch.frame ctx run #[step] #[live] {} 180 40 "completed").toList
    assertTrue ((text.splitOn "1.0 MiB").length > 1 && (text.splitOn "LAST VIEW").length > 1) "Final snapshot lost its sample"
    for label in ["9.0 GiB", "999.00%", "HISTORY", "Step ", "report worker"] do
      assertTrue ((text.splitOn label).length == 1) s!"Final view contains live stats or timeline: {label}"
    let restarted := { step with
      event := { step.event with seq := 2 },
      resources := some { incarnation := "new", timeNs := 2 } }
    assertEq (SnapshotMetrics.samples #[step, restarted] "worker1").size 1 "Meter window crossed a restart"⟩,
  ⟨"console.watch-snapshot-is-bounded-by-branches-and-workers", do
    let steps := (Array.range 500).map fun i => ({
      timestamp := toString i
      event := ⟨"boot", i, i, "worker1", some 1, s!"0:{i}", "execute", "work", "run", some "site"⟩
      resources := some { incarnation := "boot", timeNs := i + 1 } } : Trace.Step)
    let latest := Trace.latest steps
    assertEq latest.size 30 "The last view grew into an execution history"
    assertEq (latest.back?.map (·.event.seq)) (some 499)
    assertEq ((Trace.latest latest).map (·.id)) (latest.map (·.id)) "Compacting a snapshot changed it"⟩,
  ⟨"console.trace-legacy-cache-and-resource-roundtrip", do
    let event : ExecutionEvent := ⟨"boot", 1, 10, "worker1", some 0, "0:0", "execute", "work", "run", some "work"⟩
    let legacy := Json.mkObj [("timestamp", toJson "stamp"), ("event", toJson event)]
    let old ← unwrap (fromJson? (α := LeanCloudCli.Trace.Step) legacy)
    assertTrue old.resources.isNone "Legacy trace fabricated a sample"
    let sample : ResourceSample := { incarnation := "boot", timeNs := 1000, memory := some 1234 }
    let json := (toJson event).setObjVal! "resources" (toJson sample)
    let some step := LeanCloudCli.Trace.parse ("stamp @lean-cloud " ++ json.compress)
      | throw (IO.userError "Could not read recorded telemetry")
    assertEq (step.resources >>= (·.memory)) (some 1234)
    let cached ← unwrap (fromJson? (α := LeanCloudCli.Trace.Step) (toJson step))
    assertEq (cached.resources >>= (·.memory)) (some 1234)⟩
]
end LeanCloudTests
