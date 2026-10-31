import LeanCloudTests.Support
import LeanCloudCli.Console
import LeanCloud.Source

namespace LeanCloudTests
open Lean LeanCloud LeanCloudCli

def consoleCases : Array TestCase := #[
  ⟨"console.watch-shared-progress-is-one-versioned-counter", do
    let update (worker : String) (count : Nat) : Trace.Step := {
      timestamp := "1"
      event := ⟨"boot", count, 0, worker, some 0, "0:1", "progress", "", "run", none⟩
      progress := some ("build", {
        completed := count, total := some 100
        message := "Modules finished", shared := some "modules", revision := count }) }
    let steps := #[update "w1" 51, update "w2" 60, update "w1" 55]
    assertEq ((Watch.sharedProgressLines steps).map Styled.plain)
      #["60/100 · 60% · Modules finished"]
      "Shared progress regressed or added overlapping snapshots"
    assertTrue (Watch.progressLines steps).isEmpty "Shared progress was repeated inside worker cards"
    let progress : ProgressUpdate := { message := "Building", completed := 1, total := some 2 }
    let decoded : ProgressUpdate ← IO.ofExcept (fromJson? (toJson progress))
    assertEq decoded progress⟩,
  ⟨"console.watch-progress-command-and-attempt", do
    let event : ExecutionEvent := ⟨"boot", 1, 0, "worker1", some 2, "0:1", "execute", "build", "run", some "site"⟩
    let current : Trace.Step := { timestamp := "1", event }
    let progress : Trace.Step := { current with
      event := { event with seq := 2, activity := "progress" }
      progress := some ("lane", { completed := 3, total := some 4, message := "Module" }) }
    let render := fun steps => String.intercalate "\n" ((Watch.progressLines steps).map (fun line => Styled.render line 120 false)).toList
    assertTrue ((render #[current, progress]).contains '3') "Progress is missing"
    assertTrue (((render #[current, progress]).splitOn "75%").length > 1) "Percentage is missing"
    for stale in #[{ progress with event := { progress.event with attempt := some 1 } },
        { progress with event := { progress.event with session := "old" } },
        { progress with event := { progress.event with location := "0:0" } }] do
      assertEq (Watch.progressLines #[current, stale]).size 0 "Progress leaked from earlier execution"
    let next := { current with event := { event with location := "0:2" } }
    assertEq (Watch.progressLines #[current, progress, next]).size 0 "New command kept old progress"
    let finished := { current with event := { event with activity := "recorded" } }
    assertEq (Watch.progressLines #[current, progress, finished]).size 1 "Completion lost the last progress view"
    assertEq (Watch.progressLines #[current, progress] 0).size 0
    assertEq (Watch.progressLines #[{ current with event := { event with source := none } }, progress]).size 1
      "An unannotated exec cannot report progress"⟩,
  ⟨"console.watch-one-latest-message-per-builder", do
    let event : ExecutionEvent := ⟨"boot", 0, 0, "worker1", some 2, "0:1", "execute", "build", "run", none⟩
    let current : Trace.Step := { timestamp := "0", event }
    let update (seq : Nat) (slot : String) (value : ProgressUpdate) : Trace.Step := {
      timestamp := toString seq
      event := { event with seq, activity := "progress" }
      progress := some (slot, value) }
    let builders := (Array.range 10).reverse.map fun i =>
      update (i + 1) s!"builder-{i + 1}" { message := s!"Module{i + 1}" }
    let steps := #[current] ++ builders ++ #[
      update 11 "build" { completed := 5170, total := some 9031, message := "Committed modules known" },
      update 12 "builder-2" { message := "NextModule" }]
    let expected := #["build: 5170/9031 · 57% · Committed modules known"] ++
      (Array.range 10).map fun i => s!"builder-{i + 1}: {if i == 1 then "NextModule" else s!"Module{i + 1}"}"
    assertEq ((Watch.progressLines steps).map Styled.plain) expected
      "Progress must show the counter first and every builder's latest message in numeric order"
    let refreshed := steps.push (update 13 "builder-1" { message := "AnotherModule" })
    assertEq ((Watch.progressLines refreshed).map Styled.plain) (expected.set! 1 "builder-1: AnotherModule")
      "A builder update moved other rows or kept an old message"⟩,
  ⟨"console.watch-reported-worker-identities", do
    let ctx : Context := ⟨"/work", "deployment"⟩
    let steps : Array Trace.Step := #[{
      timestamp := "1", event := ⟨"session", 1, 1, "gpu-east", some 0, "0:0", "execute", "", "run", none⟩ }]
    let history : Array History := #[⟨ctx.node "cpu-west", #[], true⟩, ⟨ctx.node "gpu-east", #[], true⟩]
    assertEq (Watch.workerRoster ctx steps history) #["cpu-west", "gpu-east"]
    assertEq (Watch.workerRoster ctx steps #[]) #["gpu-east"]⟩,
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
  ⟨"console.watch-final-source", do
    let ctx : Context := ⟨"/work", "test"⟩
    let source : ProgramSource := ⟨"Example.lean", "cloud {\n  Cloud.exec work\n}", #[{ id := "work", line := 2, endLine := 2 }]⟩
    let info : ProgramInfo := ⟨"example/v1", "unit/v1", "nat/v1", "", none, #[source]⟩
    let run : Run := ⟨"run-1", "image", info, Json.null⟩
    let event : ExecutionEvent := ⟨"boot", 1, 20, "worker1", some 2, "0:1", "execute", "work", run.id, some "work"⟩
    let step : LeanCloudCli.Trace.Step := { timestamp := "2026-01-01T00:00:00.000000000Z", event }
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
    let old : LeanCloudCli.Trace.Step := { timestamp := "2026-01-01T00:00:01.000000000Z", event }
    let new : LeanCloudCli.Trace.Step := {
      timestamp := "2026-01-01T00:00:02.000000000Z"
      event := { event with session := "new", seq := 0, elapsedMs := 0 } }
    assertEq ((LeanCloudCli.Trace.merge #[new] #[old, new]).map (·.id)) #[old.id, new.id]⟩,
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
    let run : Run := ⟨"run", "image", ⟨"app/v1", "unit", "nat", "", none, #[]⟩, Json.null⟩
    let step : Trace.Step := {
      timestamp := "1"
      event := ⟨"session", 1, 1, "worker1", some 0, "0:0", "execute", "", run.id, none⟩
      resources := some {
        incarnation := "boot", timeNs := 1000000000, nodeName := some "original-machine",
        memory := some 1048576, memoryLimit := some 4194304 } }
    let live : History := ⟨ctx.node "worker1", #[{
      incarnation := "now", timeNs := 10,
      nodeName := some "replacement-machine", memory := some 9663676416 }], true⟩
    let text := String.intercalate "\n" (Watch.frame ctx run #[step] #[live] {} 180 40 "completed").toList
    assertTrue ((text.splitOn "1.0 MiB").length > 1 && (text.splitOn "LAST VIEW").length > 1) "Final snapshot lost its sample"
    assertTrue ((text.splitOn "Node original-machine").length > 1) "Final snapshot lost its original machine"
    for label in ["replacement-machine", "9.0 GiB", "999.00%", "HISTORY", "Step ", "report worker"] do
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
  ⟨"console.trace-resource-roundtrip", do
    let event : ExecutionEvent := ⟨"boot", 1, 10, "worker1", some 0, "0:0", "execute", "work", "run", some "work"⟩
    let sample : ResourceSample := {
      incarnation := "boot", timeNs := 1000, memory := some 1234,
      nodeName := some "node", hostname := some "pod", cpuCores := some 4,
      memoryCapacity := some 17179869184, cpuCapacityMillis := some 500 }
    let step : Trace.Step := { timestamp := "stamp", event, resources := some sample }
    assertEq (step.resources >>= (·.memory)) (some 1234)
    let cached ← unwrap (fromJson? (α := LeanCloudCli.Trace.Step) (toJson step))
    assertEq (cached.resources >>= (·.memory)) (some 1234)
    assertEq (cached.resources.map toJson) (some (toJson sample))⟩
]
end LeanCloudTests
