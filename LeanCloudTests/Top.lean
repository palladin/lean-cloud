import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open Lean LeanCloudCli

private def ctx : Context := ⟨"/work", "demo"⟩
private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1
private def keys (text : String) : List UInt32 := text.toUTF8.data.toList.map (·.toUInt32)

private def actors : Array Node := (Array.range 8).map fun i =>
  let run := if i < 4 then "first" else "second"
  let role := if i % 4 == 3 then "scheduler" else s!"worker{i % 4 + 1}"
  { name := s!"demo-{run}-{role}", role, run := some run, state := "running", started := "boot" }

private def inventory : Array Node := actors ++ #[
  { name := "demo-worker1-mailbox", role := "worker1-mailbox", state := "running", started := "boot" },
  { name := "demo-blobs", role := "blobs", state := "running", started := "boot" }]

private def process (call : ConsoleModel.Invocation) : Except String ProcessOutput := do
  unless call.command == "docker" do throw "Unexpected command"
  let output ← match call.args[0]? with
    | some "ps" => pure (String.intercalate "\n" (inventory.map (·.name)).toList)
    | some "inspect" =>
      let rows := inventory.map fun n =>
        let labels := Json.mkObj ([("lean-cloud.role", toJson n.role)] ++
          n.run.toList.map (fun run => ("lean-cloud.run", toJson run)))
        Json.mkObj [("Name", toJson ("/" ++ n.name)),
          ("State", Json.mkObj [("Status", toJson n.state), ("StartedAt", toJson n.started)]),
          ("Config", Json.mkObj [("Labels", labels)])]
      pure (toJson rows).compress
    | some "stats" =>
      pure (String.intercalate "\n" (inventory.filter (fun n => call.args.contains n.name) |>.map fun n =>
        (Json.mkObj [("Name", toJson n.name), ("CPUPerc", toJson "12.5%"),
          ("MemUsage", toJson "1MiB / 2MiB"), ("NetIO", toJson "1kB / 2kB"),
          ("BlockIO", toJson "3kB / 4kB")]).compress).toList)
    | some "exec" => pure "Filesystem 1024-blocks Used Available Capacity Mounted\ndisk 2048 1024 1024 50% /\n"
    | _ => throw s!"Unexpected Docker request: {reprStr call.args}"
  return { stdout := output }

private def initial : ConsoleModel.World := { process, keys := [113] }

private def checked (program : Cli α) (world := initial) : IO (α × ConsoleModel.World) := do
  let (result, world) := ConsoleModel.run program world
  return (← unwrap result, world)

def topCases : Array TestCase := #[
  ⟨"console.top.all-runs-without-workflow-files", do
    let (_, world) ← checked (command ctx ["top", "--once"])
    for node in actors do assertTrue (has world.stdout node.name) s!"Missing node {node.name}"
    assertTrue (!has world.stdout "mailbox" && !has world.stdout "demo-blobs") "Infrastructure mixed with actors"
    for metric in ["CPU", "Mem", "Disk", "Net RX", "Net TX", "I/O R", "I/O W"] do
      assertTrue (has world.stdout metric) s!"Missing graph {metric}"
    assertTrue (!world.trace.contains "readFile" && !world.trace.contains "enterTerminal" &&
      !world.trace.contains "key" && !world.stdout.contains '\x1b') "Snapshot needed workflow metadata or a TTY"
    assertEq (world.processes.filter (·.args[0]? == some "stats")).size 1
    assertTrue (world.processes.all (fun call =>
      if call.args[0]? == some "stats" || call.args[0]? == some "exec" then
        !call.args.contains "demo-blobs" && !call.args.contains "demo-worker1-mailbox" else true))
      "Sampled shared services in actor dashboard"⟩,
  ⟨"console.top.paging-and-refresh", do
    let (_, world) ← checked (command ctx ["top"])
      { initial with keys := keys "\x1b[6~\x1b[5~" ++ List.replicate 10 0 ++ [113] }
    assertTrue (has world.stdout "2/2" && has world.stdout "1/2") "Paging did not redraw"
    assertEq (world.processes.filter (·.args[0]? == some "stats")).size 2
    assertTrue (has world.stdout "0 B/s") "Second sample did not produce measured rates"
    assertTrue (world.keys.isEmpty && !world.terminal) "Top did not quit/restore terminal"
    assertTrue (world.stdout.endsWith "\x1b[?1049l") "Alternate screen not restored"⟩,
  ⟨"console.top.resize-and-no-color", do
    let (_, world) ← checked (command ctx ["top"]) { initial with
      sizes := [(120, 35), (80, 24)], keys := [0, 113], envs := #[("NO_COLOR", "1")] }
    assertTrue (has world.stdout "1/2" && has world.stdout "1/4") "Resize did not adjust the grid"
    assertTrue (!has world.stdout "\x1b[0;32m" && !has world.stdout "\x1b[0;30;46m") "Ignored NO_COLOR"⟩,
  ⟨"console.top.non-tty-and-empty-deployment", do
    let (_, world) ← checked (command ctx ["top"]) { initial with terminalAvailable := false }
    assertTrue (!world.stdout.contains '\x1b' && !world.trace.contains "key") "Non-TTY command did not return"
    let (_, world) ← checked (command ctx ["top", "--once"]) { initial with process := fun _ => .ok {} }
    assertTrue (has world.stdout "No workers or schedulers") "Empty deployment had no explanation"
    assertEq world.processes.size 2 "Empty dashboard queried stats or filesystem"⟩,
  ⟨"console.top.missing-metrics-do-not-look-idle", do
    let offline (call : ConsoleModel.Invocation) :=
      if call.args[0]? == some "stats" then .error "Stats offline"
      else if call.args[0]? == some "exec" then .error "Node disappeared"
      else process call
    let (_, world) ← checked (command ctx ["top", "--once"]) { initial with process := offline }
    assertTrue (has world.stdout "Stats unavailable: Stats offline" && has world.stdout "No sample")
      "Missing statistics looked like zero usage"
    assertTrue (!has world.stdout "0.00%") "Fabricated zero CPU on missing sample"⟩,
  ⟨"console.top.frame-bounds-and-stale-samples", do
    let history : Array History := actors.map fun n =>
      ⟨n.name, #[⟨1000, n.started, 12500, 1048576, 2097152, 0, 0, 0, 0⟩], true⟩
    for width in [0, 5, 39, 40, 80, 110, 120, 180] do
      for height in [0, 5, 13, 14, 24, 35] do
        let view := Top.frame "test" actors history #[] 100 width height
        assertTrue (view.size ≤ height - 1 && view.all (·.length ≤ width - 1)) "Dashboard escaped terminal bounds"
    let node := actors[0]!
    for stale in [history.map (fun h => { h with fresh := false }),
        history.map (fun h => { h with points := h.points.map (fun p => { p with session := "old-boot" }) })] do
      let view := Top.frame "test" #[node] stale #[] 0 120 35
      assertTrue (view.any (fun line => has line "No sample")) "Used stale or pre-restart sample"
    let view := Top.frame "test" #[{ node with state := "exited" }] history #[] 0 120 35
    assertTrue (view.any (fun line => has line "process is stopped")) "Stopped node displayed as live"⟩,
  ⟨"console.top.terminal-cleanup-on-error", do
    let (_, success) ← checked (command ctx ["top"])
    for index in [:success.trace.size] do
      if success.trace[index]! == "leaveTerminal" then continue
      let (_, world) := ConsoleModel.run (command ctx ["top"]) { initial with failAt := some index }
      assertTrue (!world.terminal && world.locks.isEmpty && world.children.isEmpty)
        s!"Top leaked resources at {index}: {success.trace[index]!}"⟩,
  ⟨"console.top.shell-handoff-and-completion", do
    let (_, world) ← checked (application []) { initial with keys := keys "top\rqhelp\rquit\r" }
    assertTrue (world.keys.isEmpty && !world.terminal) "Top did not return to anchored shell"
    assertEq (world.trace.filter (· == "enterTerminal")).size 3
    assertEq (world.trace.filter (· == "leaveTerminal")).size 3
    assertTrue (has world.stdout "Commands:" && has world.stdout "I/O W") "Dashboard or subsequent command missing"
    assertEq ((Completion.candidates {} (Completion.context "top --" 6)).map (·.value)) #["--once"]
    assertEq ((Completion.candidates {} (Completion.context "to" 2)).map (·.value)) #["top"]⟩
]

end LeanCloudTests
