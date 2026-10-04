import LeanCloudTests.Support
import LeanCloudCli.Console
import LeanCloud.Source

namespace LeanCloudTests
open Lean LeanCloud LeanCloudCli

private def basicSample (time : Nat) (session := "boot-1") (rx := 0) : Sample :=
  ⟨time, session, 12500, 1048576, 2097152, rx, 0, 0, 0⟩

def consoleCases : Array TestCase := #[
  ⟨"console.watch.elastic-worker-pages", do
    let page := Watch.navigate #[] 1 2 {} (.text "]") 12
    assertEq page.workerPage 1
    let fourth := Watch.navigate #[] 1 2 page (.text "1") 12
    assertEq fourth.worker (some "worker4")
    let last := Watch.navigate #[] 1 2 {} .backTab 12
    assertEq last.worker (some "worker12")
    assertEq last.workerPage 3
    assertTrue (Watch.navigate #[] 1 2 last .tab 12).worker.isNone "Tab did not return to Global"
    assertTrue (Watch.navigate #[] 1 2 {} .tab 0).worker.isNone "Zero-worker pool selected a nonexistent worker"⟩,
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
  ⟨"console.watch-historical-source", do
    let ctx : Context := ⟨"/work", "test"⟩
    let source : ProgramSource := ⟨"Example.lean", "cloud {\n  Cloud.exec work\n}", #[⟨"work", 2⟩]⟩
    let info : ProgramInfo := ⟨"example/v1", "unit/v1", "nat/v1", "", none, some source⟩
    let run : Run := ⟨"run-1", "image", info, Json.null, defaultWorkerCount⟩
    let event : ExecutionEvent := ⟨"boot", 1, 20, "worker1", some 2, "0:1", "execute", "work", run.id⟩
    let step : LeanCloudCli.Trace.Step := ⟨"2026-01-01T00:00:00.000000000Z", event, none⟩
    let node : Node := { name := ctx.node "worker1", state := "exited", started := "boot", role := "worker1" }
    for status in ["completed", "paused", "cancelled", "result pending"] do
      let lines := Watch.frame ctx run #[node] #[step] #[] {} 120 35 status
      assertTrue (lines.any (fun l => (l.splitOn "2   > ").length > 1)) "Historical source marker absent"
      assertTrue (lines.any (fun l => (l.splitOn status).length > 1)) "Run status absent"
      let label := if status == "result pending" then "LIVE stats" else "Stats: not recorded"
      assertTrue (lines.any (fun l => (l.splitOn label).length > 1)) "Metric mode was not labeled"
    for width in [20, 40, 80, 120, 220] do
      for height in [8, 16, 24, 45] do
        let lines := Watch.frame ctx run #[node] #[step] #[] {} width height
        assertTrue (lines.size < height && lines.all (·.length < width)) "Watch exceeds terminal dimensions"⟩,
  ⟨"console.watch-cursor-survives-refresh", do
    let steps := (Array.range 5).map fun n =>
      ({ timestamp := toString (n + 1), event := ⟨"boot", n, n, "worker1", some 0, "0:1", "execute", "work", "run"⟩ } : LeanCloudCli.Trace.Step)
    let back := Watch.navigate steps 1 2 {} .left
    assertEq (Watch.index steps back) 3
    let first := Watch.navigate steps 1 2 back .home
    assertEq (Watch.index steps first) 0
    let page := Watch.navigate steps 1 2 first .pageDown
    assertEq (Watch.index steps page) 2
    let late := { steps[0]! with timestamp := "0" }
    let refreshed := LeanCloudCli.Trace.merge steps #[late, { steps[4]! with timestamp := "6" }]
    assertEq (Watch.index refreshed back) 4 "Inserted observations moved the selected event"
    let follow := Watch.navigate refreshed 1 2 back .end
    assertTrue follow.cursor.isNone "End did not follow"
    assertEq (Watch.index refreshed follow) 6
    assertEq (Watch.index #[] (Watch.navigate #[] 1 5 {} .left)) 0⟩,
  ⟨"console.trace-order-and-dedup", do
    let event : ExecutionEvent := ⟨"old", 90, 9999, "worker1", some 2, "0:1", "execute", "work", "run"⟩
    let old : LeanCloudCli.Trace.Step := ⟨"2026-01-01T00:00:01.000000000Z", event, none⟩
    let new : LeanCloudCli.Trace.Step := ⟨"2026-01-01T00:00:02.000000000Z", { event with session := "new", seq := 0, elapsedMs := 0 }, none⟩
    let parsed := LeanCloudCli.Trace.parse (old.timestamp ++ " @lean-cloud " ++ (toJson event).compress)
    assertEq (parsed.map (·.id)) (some old.id)
    assertEq ((LeanCloudCli.Trace.merge #[new] #[old, new]).map (·.id)) #[old.id, new.id]
    assertTrue (LeanCloudCli.Trace.parse "ordinary output").isNone "Ordinary log became a step"⟩,
  ⟨"console.watch-global-and-worker-views", do
    let steps := (Array.range 6).map fun n =>
      ({ timestamp := toString n, event := ⟨"boot", n, n, if n % 2 == 0 then "worker1" else "worker2",
        some 0, s!"0:{n}", "execute", "work", "run"⟩ } : LeanCloudCli.Trace.Step)
    let browsing := Watch.navigate steps 1 2 {} .left
    let focused := Watch.navigate steps 1 2 browsing (.text "2")
    assertEq focused.worker (some "worker2")
    assertEq ((Watch.visible steps focused).map (·.event.seq)) #[1, 3, 5]
    assertEq focused.cursor (some steps[3]!.id) "Focusing a worker jumped out of historical context"
    let previous := Watch.navigate steps 1 2 focused .left
    assertEq previous.cursor (some steps[1]!.id) "Worker navigation crossed into another worker"
    let global := Watch.navigate steps 1 2 previous (.text "g")
    assertTrue global.worker.isNone "g did not return to all workers"
    assertEq global.cursor previous.cursor "Returning to overview moved the cursor"
    assertEq (Watch.visible steps global).size 6
    let latest := Watch.navigate steps 1 2 focused .end
    assertEq (Watch.index (Watch.visible steps latest) latest) 2
    assertTrue latest.cursor.isNone "Local follow did not follow the chosen worker"
    let tab1 := Watch.navigate steps 1 2 {} .tab
    assertEq tab1.worker (some "worker1")
    let tab2 := Watch.navigate steps 1 2 tab1 .tab
    assertEq tab2.worker (some "worker2")
    let tab3 := Watch.navigate steps 1 2 tab2 .tab
    assertEq tab3.worker (some "worker3")
    assertTrue (Watch.navigate steps 1 2 tab3 .tab).worker.isNone "Tab did not cycle back to Global"
    ⟩,
  ⟨"console.recorded-metric-rates-and-restarts", do
    let before : ResourceSample := {
      incarnation := "boot", timeNs := 1000000000,
      cpuNs := some 100000000, rx := some 100 }
    let after := { before with timeNs := 2000000000, cpuNs := some 600000000, rx := some 1100 }
    assertEq (RecordedMetrics.rate before after (·.cpuNs) 100000) (some 50000)
    assertEq (RecordedMetrics.rate before after (·.rx)) (some 1000)
    assertEq (RecordedMetrics.rate before { after with incarnation := "restarted" } (·.cpuNs)) none
    assertEq (RecordedMetrics.rate before { after with rx := some 0 } (·.rx)) none
    assertEq (RecordedMetrics.rate before { after with rx := none } (·.rx)) none
    assertEq (RecordedMetrics.rate before before (·.cpuNs)) none⟩,
  ⟨"console.history-global-panels-never-use-future-or-live-stats", do
    let ctx : Context := ⟨"/work", "test"⟩
    let source : ProgramSource := ⟨"Code.lean", "first\ndo_worker_one\nsecond\ndo_worker_two\nthird\ndo_worker_three",
      #[⟨"one", 2⟩, ⟨"two", 4⟩, ⟨"three", 6⟩]⟩
    let run : Run := ⟨"run", "image", ⟨"app/v1", "unit", "nat", "", none, some source⟩, Json.null, defaultWorkerCount⟩
    let steps := (Array.range 3).map fun i =>
      ({ timestamp := s!"2026-01-01T00:00:0{i}.000000000Z"
         event := ⟨"session", i, i, s!"worker{i + 1}", some 0, s!"0:{i}", "execute", #["one", "two", "three"][i]!, run.id⟩
         resources := some {
           incarnation := s!"boot{i}", timeNs := (i + 1) * 1000000000,
           memory := some ((i + 1) * 1048576), memoryLimit := some 4194304 } } : LeanCloudCli.Trace.Step)
    let future := { steps[0]! with
      timestamp := "2026-01-01T00:00:09.000000000Z",
      resources := some { incarnation := "new", timeNs := 9000000000, memory := some 9663676416 } }
    let live : History := ⟨ctx.node "worker1", #[⟨10, "now", 999000, 9663676416, 99999999999, 0, 0, 0, 0⟩], true⟩
    let nav : Watch.Navigation := { cursor := some steps[2]!.id }
    let view := Watch.frame ctx run #[] (steps.push future) #[live] nav 207 45 "result pending"
    let text := String.intercalate "\n" view.toList
    for label in ["worker1", "worker2", "worker3", "do_worker_one", "do_worker_two", "do_worker_three",
        "1.0 MiB", "2.0 MiB", "3.0 MiB", "HISTORY"] do
      assertTrue ((text.splitOn label).length > 1) s!"Global view lost {label}"
    for label in ["9.0 GiB", "999.00%", "LIVE stats"] do
      assertTrue ((text.splitOn label).length == 1) s!"History leaked future/live data: {label}"
    let oldSteps := steps.map fun step => { step with resources := none }
    let text := String.intercalate "\n" (Watch.frame ctx run #[] oldSteps #[live] {} 207 45 "completed").toList
    assertTrue ((text.splitOn "Stats: not recorded").length > 1) "Old logs fabricated metrics"
    assertTrue ((text.splitOn "999.00%").length == 1) "Old logs fell back to live stats"
    let restarted := steps.push { future with event := { future.event with worker := "worker1" } }
    assertEq (RecordedMetrics.history restarted "worker1").size 1 "History crossed a container restart"⟩,
  ⟨"console.trace-legacy-cache-and-resource-roundtrip", do
    let event : ExecutionEvent := ⟨"boot", 1, 10, "worker1", some 0, "0:0", "execute", "work", "run"⟩
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
