import LeanCloudTests.Support
import LeanCloudCli.Watch

namespace LeanCloudTests.BranchTree
open Lean LeanCloud LeanCloudCli

private def jobStep (seq : Nat) (job : Scheduler.Job) : Trace.Step := {
  timestamp := s!"2026-01-01T00:00:{pad 2 (toString seq)}Z"
  event := ⟨"scheduler", seq, seq, "scheduler", none, job.location.key, "branch-state", "", "run", none⟩
  branch := some job.branch
  job := some (BranchObservation.ofJob job) }

private def workerStep (seq : Nat) (branch : Location) (location := Location.root)
    (source := "child") : Trace.Step := {
  timestamp := s!"2026-01-01T00:00:{pad 2 (toString seq)}Z"
  event := ⟨"worker", seq, seq, "worker2", some 1, location.key, "execute", source, "run", some source⟩
  branch := some branch }

private def fork : Location := #[(0, 2)]
private def child := fork.child 0
private def sibling := fork.child 1
private def nestedFork := child.next
private def grandchild := nestedFork.child 0

private def expandedTree : LeanCloudCli.BranchTree.Navigation := {
  expanded := .ofList [("parallel/0:2", true), ("parallel/0:2/0:1", true)] }

private def steps : Array Trace.Step := #[
  jobStep 0 ⟨Location.root, fork, false, .waiting #[child, sibling]⟩,
  jobStep 1 ⟨child, child, false, .running "worker2" 1 100⟩,
  jobStep 2 ⟨sibling, sibling, false, .pending⟩,
  workerStep 3 child Location.root "ancestor",
  workerStep 4 child child "child",
  jobStep 5 ⟨child, nestedFork, false, .waiting #[grandchild]⟩,
  jobStep 6 ⟨grandchild, grandchild, false, .pending⟩,
  jobStep 7 ⟨grandchild, grandchild, false, .done⟩,
  jobStep 8 ⟨child, nestedFork, true, .done⟩,
  jobStep 9 ⟨sibling, sibling, false, .done⟩,
  jobStep 10 ⟨Location.root, fork, true, .done⟩ ]

private def run : Run := {
  id := "run", image := "image", input := Json.null
  program := ⟨"example", "unit", "nat", "", none, #[⟨"Example.lean",
    "cloud {\n  ancestor_code\n  child_code\n}", #[{ id := "ancestor", line := 2, endLine := 2 },
      { id := "child", line := 3, endLine := 3 }]⟩]⟩ }

private def text (nav : Watch.Navigation) (width := 180) (height := 40) (trace := steps) : String :=
  String.intercalate "\n" (Watch.frame ⟨"/work", "test"⟩ run trace #[] nav width height "completed").toList

private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1

public def cases : Array TestCase := #[
  ⟨"console.tree.parallel-labels-survive-replay-and-completion", do
    let labeled (seq : Nat) (owner location : Location) (label : String) :=
      { workerStep seq owner location with event := {
        (workerStep seq owner location).event with
        activity := "parallel-label", operation := label, source := none } }
    -- Child replay visits the parent's fork; its label belongs to the fork,
    -- while worker ownership still determines which code pane is current.
    let observed := steps ++ #[labeled 11 grandchild fork "200/9,031 · 2%",
      labeled 12 grandchild nestedFork "nested work", workerStep 13 grandchild grandchild]
    let compact := Trace.latest (Trace.merge #[] observed)
    let cached ← unwrap (fromJson? (α := Array Trace.Step) (toJson compact))
    let entries := LeanCloudCli.BranchTree.current cached
    let rows := LeanCloudCli.BranchTree.rows entries expandedTree
    assertEq ((rows.find? (·.key == "parallel/0:2")).map (·.title)) (some "200/9,031 · 2%")
    assertEq ((rows.find? (·.key == "parallel/0:2/0:1")).map (·.title)) (some "nested work")
    assertEq ((rows.find? (·.key == "parallel/0:2")).map (·.status)) (some "2/2")
    for width in [100, 180] do
      let frame := text { tree := { selected := some "parallel/0:2" } } width (trace := cached)
      assertTrue (has frame "200/9,031 · 2%" && !has frame "parallel @") "Watch lost the short label"
      assertTrue (!has frame "Parallel 0:2") "Code panel exposed the internal parallel location"
    let empty := Trace.latest (Trace.merge compact #[labeled 14 child fork ""])
    let rows := LeanCloudCli.BranchTree.rows (LeanCloudCli.BranchTree.current empty) {}
    assertEq (rows[1]?.map (·.title)) (some "parallel")⟩,
  ⟨"console.tree.large-scheduler-snapshot", do
    let count := 10000
    let jobs := (Array.range count).map fun i =>
      BranchObservation.ofJob ⟨fork.child i, fork.child i, false, .done⟩
    let root := BranchObservation.ofJob ⟨Location.root, fork, true, .running "worker4" 9 100⟩
    let entries := LeanCloudCli.BranchTree.current steps (jobs.push root)
    assertEq (LeanCloudCli.BranchTree.rows entries {}).size 2 "Large parallel group expanded by default"
    let rows := LeanCloudCli.BranchTree.rows entries expandedTree
    assertEq (rows.filter fun row => row.parent == some "parallel/0:2").size count
    assertEq (rows[0]?.map (·.status)) (some "worker4") "Paged observations overrode current scheduler state"
    assertEq (LeanCloudCli.BranchTree.rows entries { expanded := .ofList [("branch/0:0", false)] }).size 1
    let last := LeanCloudCli.BranchTree.navigate entries expandedTree .up
    assertEq last.selected (some "branch/0:2/9999:0")
    let view := LeanCloudCli.BranchTree.lines entries last 12 52
    assertTrue (view.any (fun line => has (Styled.plain line) "branch 9999")) "Wrapped selection stayed off screen"⟩,
  ⟨"console.tree.parallel-shows-workers-branch-shows-current-assignment", do
    let other := { workerStep 5 sibling sibling "ancestor" with event := {
      (workerStep 5 sibling sibling "ancestor").event with worker := "worker3" } }
    let active := (steps.extract 0 5) ++ #[jobStep 5 ⟨sibling, sibling, false, .running "worker3" 1 100⟩, other]
    let ctx : Context := ⟨"/work", "test"⟩
    let histories : Array History := (Array.range 3).map fun i => ⟨ctx.node s!"worker{i+1}", #[{
      incarnation := "boot", timeNs := 1, nodeName := some s!"machine-{i+1}",
      cpuCores := some 8, memoryCapacity := some 17179869184,
      cpuCapacityMillis := some 2000, memory := some 1048576, memoryLimit := some 536870912 }], true⟩
    let view (selection : String) (trace := active) := String.intercalate "\n"
      (Watch.frame ctx run trace histories { tree := { expandedTree with selected := some selection } } 220 50 "result pending").toList
    let group := view "parallel/0:2"
    for worker in ["worker1", "worker2", "worker3"] do
      assertTrue (has group worker) s!"Parallel group omitted {worker}"
    assertTrue (has group "worker1 · idle" && has group "worker2 · branch 0:2/0:0" &&
      has group "worker3 · branch 0:2/1:0") "Worker cards lost current assignments"
    assertTrue (has group "Example.lean:3" && has group "Example.lean:2") "Workers did not show their own source locations"
    for machine in ["machine-1", "machine-2", "machine-3"] do
      assertTrue (has group ("Node " ++ machine)) "Parallel group lost worker placement"
    for metric in ["8 logical CPUs", "16.0 GiB RAM", "I/O W"] do
      assertTrue (has group metric) "Worker card clipped machine information or graphs"
    for page in [:3] do
      let narrow := String.intercalate "\n" (Watch.frame ctx run active histories
        { tree := { selected := some "parallel/0:2" }, workers := page } 120 35 "result pending").toList
      assertTrue (has narrow s!"worker{page + 1} ·") "Paging did not make every worker reachable"
    let selected := view "branch/0:2/0:0"
    assertTrue (has selected "worker2 · executing" && !has selected "worker3 · executing") "Branch showed another worker"
    assertTrue (has selected "Node machine-2" && !has selected "Node machine-3") "Branch showed another machine"
    let done := view "branch/0:2/0:0" (active.push (jobStep 6 ⟨child, child, false, .done⟩))
    assertTrue (has done "No worker executing this branch" && !has done "worker2 · executing") "Completed branch kept its old live worker"
    let retry := active.push (jobStep 6 ⟨child, child, false, .running "worker2" 2 200⟩)
    assertTrue (Watch.executing retry (LeanCloudCli.BranchTree.current retry) "worker2").isEmpty
      "New attempt showed revoked execution as current"
    for removed in ["HISTORY", "Step ", "report worker", "mapped step", "[/]"] do
      assertTrue (!has group removed) s!"Removed timeline remains: {removed}"⟩,
  ⟨"console.tree.nested-forks-and-latest-state", do
    let early := LeanCloudCli.BranchTree.current (steps.extract 0 1)
    assertEq early.size 3 "A fork must expose children that have not reached a worker"
    assertTrue (early.any (fun e => e.branch == sibling && e.job.isNone)) "Missing event fabricated child state"
    let earlyRows := LeanCloudCli.BranchTree.rows early {}
    assertTrue (!earlyRows.any (·.branch == grandchild)) "Future descendant appeared in history"
    let current := LeanCloudCli.BranchTree.current #[] #[steps[0]!.job.get!]
    assertEq current.size 3 "Paged telemetry hid pending children from the current scheduler snapshot"
    assertEq (LeanCloudCli.BranchTree.rows current expandedTree).size 4
    let compact := Trace.latest #[steps[0]!, steps[10]!]
    assertEq (LeanCloudCli.BranchTree.current compact).size 3 "Completion erased the parallel group when child observations were missing"
    let entries := LeanCloudCli.BranchTree.current steps
    let rows := LeanCloudCli.BranchTree.rows entries expandedTree
    assertEq rows.size 6
    assertEq (rows.filter (·.fork.isSome)).size 2
    assertEq (rows.find? (·.branch == grandchild) |>.map (·.depth)) (some 4)
    let laterFork := Location.next fork
    let trace := steps.push (jobStep 11 ⟨Location.root, laterFork, false, .waiting #[laterFork.child 0]⟩)
    assertEq ((LeanCloudCli.BranchTree.rows (LeanCloudCli.BranchTree.current trace) expandedTree).filter (·.fork.isSome)).size 3
    assertEq (LeanCloudCli.BranchTree.current (trace.extract 0 steps.size)).size entries.size⟩,
  ⟨"console.tree.parallel-defaults-and-refresh", do
    let early := LeanCloudCli.BranchTree.current (steps.extract 0 1)
    let visible := LeanCloudCli.BranchTree.rows early {}
    assertEq (visible.map (·.key)) #["branch/0:0", "parallel/0:2"]
    let initial := text {}
    assertTrue (has initial "▸ parallel" && !has initial "parallel @" && !has initial "branch 0") "Initial frame did not show a collapsed group"
    let group := LeanCloudCli.BranchTree.navigate early {} .down
    let opened := LeanCloudCli.BranchTree.navigate early group .right
    assertEq opened.selected group.selected "Expanding moved the selection"
    assertEq (LeanCloudCli.BranchTree.rows early opened).size 4
    -- A nested parallel discovered on refresh stays closed; the parent stays open.
    let refreshed := LeanCloudCli.BranchTree.current steps
    let visible := LeanCloudCli.BranchTree.rows refreshed opened
    assertEq (visible.map (·.key)) #["branch/0:0", "parallel/0:2", "branch/0:2/0:0",
      "parallel/0:2/0:1", "branch/0:2/1:0"]
    let nested := { opened with selected := some "parallel/0:2/0:1" }
    let nestedOpen := LeanCloudCli.BranchTree.navigate refreshed nested .enter
    assertEq (LeanCloudCli.BranchTree.rows refreshed nestedOpen).size 6
    let folded := LeanCloudCli.BranchTree.navigate refreshed
      { nestedOpen with selected := some "parallel/0:2" } .left
    let later := fork.next
    let refreshed := LeanCloudCli.BranchTree.current
      (steps.push (jobStep 11 ⟨Location.root, later, false, .waiting #[later.child 0]⟩))
    assertEq ((LeanCloudCli.BranchTree.rows refreshed folded).map (·.key))
      #["branch/0:0", "parallel/0:2", "parallel/0:3"] "Refresh reopened a group"
    let reopened := LeanCloudCli.BranchTree.navigate refreshed folded .right
    assertTrue ((LeanCloudCli.BranchTree.rows refreshed reopened).any (·.branch == grandchild))
      "Reopening the parent forgot a nested expansion"
    assertTrue (!(LeanCloudCli.BranchTree.rows refreshed reopened).any (·.branch == later.child 0))
      "New parallel group expanded automatically"⟩,
  ⟨"console.tree.wraps-visible-rows", do
    let entries := LeanCloudCli.BranchTree.current steps
    let nav := LeanCloudCli.BranchTree.navigate entries {} .up
    assertEq nav.selected (some "parallel/0:2")
    assertEq (LeanCloudCli.BranchTree.navigate entries nav .down).selected (some "branch/0:0")
    let opened := LeanCloudCli.BranchTree.navigate entries nav .right
    let first := { opened with selected := some "branch/0:0" }
    let last := LeanCloudCli.BranchTree.navigate entries first .up
    assertEq last.selected (some "branch/0:2/1:0") "Wrap selected a hidden descendant"
    assertEq (LeanCloudCli.BranchTree.navigate entries last .down).selected first.selected
    assertTrue (LeanCloudCli.BranchTree.navigate entries last .right == last) "Right on a leaf wrapped unexpectedly"
    let one := LeanCloudCli.BranchTree.navigate entries first .left
    for key in [Input.Key.up, .down] do
      assertEq (LeanCloudCli.BranchTree.navigate entries one key).selected (some "branch/0:0")
      assertTrue (LeanCloudCli.BranchTree.navigate #[] one key == one) "Empty tree changed selection"
    let watch := Watch.navigate steps 1 { tree := first, offset := 20, workers := 2 } .up
    assertEq watch.tree.selected last.selected
    assertEq watch.offset 0
    assertEq watch.workers 0⟩,
  ⟨"console.tree.assignment-ownership-during-replay", do
    assertEq steps[3]!.owner (some child)
    let own := LeanCloudCli.BranchTree.observations steps child
    assertEq (own.map (·.event.source)) #[some "ancestor", some "child"]
    assertTrue (LeanCloudCli.BranchTree.observations steps Location.root).isEmpty "Replay was attributed to root"
    let orphan := LeanCloudCli.BranchTree.current #[workerStep 0 grandchild]
    assertEq orphan.size 3 "Missing ancestors were not reconstructed"
    assertTrue (orphan.all (·.job.isNone)) "Inferred ancestry fabricated scheduler status"⟩,
  ⟨"console.tree.navigation-and-code-selection", do
    let active := steps.extract 0 5
    let nav : Watch.Navigation := { tree := { expandedTree with selected := some "branch/0:2/0:0" } }
    let view := text nav (trace := active)
    assertTrue (has view "Branch 0:2/0:0" && has view "3   >   child_code") "Selected branch did not show its own code"
    let up := Watch.navigate active 1 nav .up
    assertEq up.tree.selected (some "parallel/0:2")
    let folded := Watch.navigate active 1 up .left
    let entries := LeanCloudCli.BranchTree.current active
    assertEq (LeanCloudCli.BranchTree.rows entries folded.tree).size 2
    let expanded := Watch.navigate active 1 folded .right
    assertEq (LeanCloudCli.BranchTree.rows entries expanded.tree).size 4
    assertTrue ((Watch.navigate active 1 expanded (.text "[")).tree == expanded.tree) "Removed timeline keys changed selection"⟩,
  ⟨"console.tree.controls-and-legacy-traces", do
    let control (name : String) := { steps[0]! with event := { steps[0]!.event with activity := name }, branch := none, job := none }
    let frame (status : String) (trace : Array Trace.Step) := String.intercalate "\n"
      (Watch.frame ⟨"/work", "test"⟩ run trace #[] {} 180 40 status).toList
    let stopped := frame "paused" (steps.extract 0 3)
    assertTrue (has stopped "root paused" && !has stopped "root waiting")
      "Missing telemetry concealed the authoritative paused status"
    let live := frame "result pending" ((steps.extract 0 3).push (control "paused"))
    assertTrue (has live "root waiting" && !has live "root paused")
      "Stale pause telemetry overrode the live run status"
    let paused := LeanCloudCli.BranchTree.current ((steps.extract 0 3).push (control "paused"))
    assertTrue ((LeanCloudCli.BranchTree.rows paused {}).any (·.status == "paused")) "Pause not reflected"
    let resumed := LeanCloudCli.BranchTree.current ((steps.extract 0 3) ++ #[control "paused", control "resumed"])
    assertTrue (!(LeanCloudCli.BranchTree.rows resumed {}).any (·.status == "paused")) "Resume retained pause"
    let killed := LeanCloudCli.BranchTree.current (steps.push (control "sealed"))
    assertTrue ((LeanCloudCli.BranchTree.rows killed {}).filter (·.fork.isNone) |>.all (·.status == "completed"))
      "A later kill overwrote completed branches"
    let legacy := { steps[4]! with branch := none, job := none }
    assertEq legacy.owner (some child)
    assertTrue ((LeanCloudCli.BranchTree.current #[legacy]).all (·.job.isNone)) "Legacy logs fabricated states"
    assertTrue (Trace.location? "0:nope").isNone "Invalid location accepted"⟩,
  ⟨"console.tree.metadata-roundtrip", do
    let sample := steps[1]!
    let cached ← unwrap (fromJson? (α := Trace.Step) (toJson sample))
    assertEq cached.branch sample.branch
    assertEq cached.job sample.job⟩,
  ⟨"console.tree.large-parallel-observation", do
    let job : Scheduler.Job := ⟨Location.root, fork, false, .waiting ((Array.range 1000).map fork.child)⟩
    let step := jobStep 0 job
    assertTrue ((toJson step).compress.utf8ByteSize < 1500) "Large groups exceed the native trace line limit"
    let entries := LeanCloudCli.BranchTree.current #[step]
    assertEq entries.size 1001 "Parallel child count did not reconstruct all branch locations"
    assertTrue (entries.any (·.branch == fork.child 999)) "Last pending branch is missing"⟩,
  ⟨"console.tree.sidebar-layout-and-bounded-frames", do
    let view := text { tree := expandedTree } (trace := steps.extract 0 7)
    let lines := view.splitOn "\n"
    assertTrue (lines.any (fun line => has line "BRANCHES" && has line "Branch" && has line "│"))
      "Tree and worker code were not placed side by side"
    assertTrue (has view "waiting 0/1" && !has view "root completed") "Latest branch states were lost"
    for width in [40, 80, 100, 120, 180, 220] do
      for height in [16, 24, 35, 50] do
        for selection in ["branch/0:0", "parallel/0:2"] do
          let frame := Watch.frame ⟨"/work", "test"⟩ run steps #[] { tree := { selected := some selection } }
            width height "completed"
          assertTrue (frame.size < height && frame.all (·.length < width)) "Tree or worker grid overflowed terminal bounds"⟩ ]

end LeanCloudTests.BranchTree
