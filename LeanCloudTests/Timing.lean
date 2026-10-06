import LeanCloudTests.Support
import LeanCloudCli.BranchTree

namespace LeanCloudTests.Timing
open Lean LeanCloud LeanCloudCli

private def root := Location.root
private def fork : Location := #[(0, 2)]
private def child := fork.child 0
private def sibling := fork.child 1

private def initial : Pool.Run := ⟨"test", .active, {}⟩
private def waiting : Pool.Run := { initial with scheduler := { jobs := #[
  ⟨root, fork, false, .waiting #[child, sibling]⟩,
  ⟨child, child, false, .pending⟩, ⟨sibling, sibling, false, .pending⟩] } }

private def finishChild (run : Pool.Run) (location : Location) : Pool.Run :=
  { run with scheduler := { run.scheduler with jobs := run.scheduler.jobs.map fun job =>
    if job.branch == location then { job with status := .done } else job } }

def cases : Array TestCase := #[
  ⟨"timing.parallel-spans-include-waiting-and-freeze-independently", do
    let timing := LeanCloud.Timing.observe {} none initial 1000
    let timing := LeanCloud.Timing.observe timing (some initial) waiting 2000
    let left := finishChild waiting child
    let timing := LeanCloud.Timing.observe timing (some waiting) left 3500
    assertEq (timing.branches.find? (·.1 == child) |>.map (·.2.elapsed 10000)) (some 1500)
    assertEq (timing.branches.find? (·.1 == sibling) |>.map (·.2.elapsed 5000)) (some 3000)
    assertEq (timing.groups[0]?.map (·.2.finishedMs)) (some none)
    let both := finishChild left sibling
    let timing := LeanCloud.Timing.observe timing (some left) both 7000
    assertEq (timing.groups[0]?.map (·.2.elapsed 10000)) (some 5000)
    assertEq (timing.span.map (·.elapsed 10000)) (some 9000)
    let done := finishChild both root
    let timing := LeanCloud.Timing.observe timing (some both) done 8000
    let restored ← unwrap (fromJson? (α := LeanCloud.Timing.Run) (toJson timing))
    let later := LeanCloud.Timing.observe restored (some done) done 90000
    assertEq later.span timing.span
    assertEq later.branches timing.branches
    assertEq later.groups timing.groups
    assertEq (later.span.map (·.elapsed 100000)) (some 7000)⟩,
  ⟨"timing.retry-pause-and-clock-regression-do-not-reset-spans", do
    let timing := LeanCloud.Timing.observe {} none initial 1000
    let timing := LeanCloud.Timing.observe timing (some initial) waiting 2000
    let paused := { waiting with mode := .paused }
    let timing := LeanCloud.Timing.observe timing (some waiting) paused 10000
    assertEq (timing.span.map (·.elapsed timing.observedMs)) (some 9000)
    let timing := LeanCloud.Timing.observe timing (some paused) waiting 9000
    assertEq timing.observedMs 10000
    assertEq (timing.groups[0]?.map (·.2.startedMs)) (some 2000)
    assertEq (timing.branches.find? (·.1 == child) |>.map (·.2.startedMs)) (some 2000)
    assertTrue (timing.span.all (·.finishedMs.isNone)) "Pause finished the workflow"⟩,
  ⟨"timing.kill-and-failure-freeze-unfinished-branches", do
    let timing := LeanCloud.Timing.observe (LeanCloud.Timing.observe {} none initial 1000)
      (some initial) waiting 2000
    for terminal in [{ waiting with mode := .killed },
        { waiting with scheduler := { waiting.scheduler with error := some ⟨.protocol, "failed"⟩ } }] do
      let done := LeanCloud.Timing.observe timing (some waiting) terminal 5000
      assertEq (done.span.bind (·.finishedMs)) (some 5000)
      assertTrue (done.branches.all (·.2.finishedMs == some 5000)) "Branch clock still running"
      assertTrue (done.groups.all (·.2.finishedMs == some 5000)) "Group clock still running"⟩,
  ⟨"timing.legacy-state-stays-unknown-status-roundtrips", do
    let timing := LeanCloud.Timing.observe {} (some waiting) waiting 9000
    assertTrue (timing.span.isNone && timing.branches.isEmpty && timing.groups.isEmpty)
      "Recovery fabricated old start times"
    let legacy ← unwrap (fromJson? (α := LeanCloud.Timing.Status) (toJson initial.scheduler))
    assertTrue legacy.timing.isNone "Legacy status acquired a timing"
    let status : LeanCloud.Timing.Status := { toState := waiting.scheduler, timing := some timing }
    let restored ← unwrap (fromJson? (α := LeanCloud.Timing.Status) (toJson status))
    assertEq restored.toState waiting.scheduler
    assertEq restored.timing (some timing)⟩,
  ⟨"timing.format-and-tree-column", do
    for (ms, text) in [(0, "0ms"), (999, "999ms"), (1234, "1.234s"), (60000, "1m00s"),
        (3599999, "59m59s"), (3600000, "1h00m"), (86400000, "1d00h")] do
      assertEq (Time.duration ms) text
    assertEq (Time.stamp 0) "1970-01-01 00:00:00"
    assertEq (Time.stamp 86400000) "1970-01-02 00:00:00"
    let timing := LeanCloud.Timing.observe (LeanCloud.Timing.observe {} none initial 1000)
      (some initial) waiting 2000
    let entries := waiting.scheduler.jobs.map fun job => {
      branch := job.branch, job := some (BranchObservation.ofJob job) : BranchTree.Entry }
    let lines := BranchTree.lines entries {} 20 52 (some { timing with observedMs := 5432 })
    assertTrue (lines.all (Styled.length · ≤ 52)) "Elapsed column exceeded width"
    let text := String.intercalate "\n" (lines.map Styled.plain).toList
    assertTrue ((text.splitOn "ELAPSED").length > 1 && (text.splitOn "4.432s").length > 1 &&
      (text.splitOn "3.432s").length == 4) "Missing root, group, or child durations"⟩ ]

end LeanCloudTests.Timing
