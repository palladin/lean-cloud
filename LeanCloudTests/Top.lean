import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open Lean LeanCloud LeanCloudCli

private def ctx : Context := ⟨"/work", "demo"⟩
private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1
private def keys (text : String) : List UInt32 := text.toUTF8.data.toList.map (·.toUInt32)

private def actors : Array Node := (Array.range 8).map fun i =>
  let role := if i == 0 then "scheduler" else s!"worker{i}"
  { name := s!"demo-{role}", role, state := "running", resources := some #[{
      incarnation := "boot", timeNs := 1, memory := some 1048576,
      nodeName := some s!"machine-{i / 2}", hostname := some s!"{role}-0",
      cpuCores := some 8, memoryCapacity := some 17179869184,
      cpuCapacityMillis := some 1500, memoryLimit := some 536870912 }] }


private def http (nodes : Array Node) (_url _token : String) (body : Json) : Except String Json := do
  let request ← DeploymentApi.Request.decode body
  match request with
  | .nodes => return toJson (Except.ok (toJson (nodes.map fun node => ({
      id := node.role, online := node.state == "running", samples := node.resources.getD #[]
      } : DeploymentApi.Node))) : Except String Json)
  | _ => throw "Unexpected request"

private def connected (nodes := actors) : ConsoleModel.World :=
  ({ keys := [113], envs := #[("LEAN_CLOUD_TOKEN", "secret")], http := some (http nodes) } : ConsoleModel.World)
    |>.json (ctx.home / "connection.json") ({url := "http://127.0.0.1:8080", deployment := "demo", tokenEnv := "LEAN_CLOUD_TOKEN"} : Client.Connection)

private def initial := connected

private def checked (program : Cli α) (world := initial) : IO (α × ConsoleModel.World) := do
  let (result, world) := ConsoleModel.run program world
  return (← unwrap result, world)

def topCases : Array TestCase := #[
  ⟨"console.top.custom-worker-name", do
    let custom : Node := { name := "demo-gpu-east", role := "gpu-east", state := "running" }
    let (nodes, world) ← checked (ctx.nodes) (connected (actors.push custom))
    assertTrue ((Top.actors nodes).any (·.role == "gpu-east")) "Dropped externally configured worker"
    let (catalog, _) ← checked (Completion.load ctx) world
    assertTrue (catalog.actors.any (·.value == "gpu-east")) "Completion ignored reported node"⟩,
  ⟨"console.top.persistent-idle-nodes", do
    let view := Top.actors actors
    assertEq (view.map (·.role)) (#["scheduler"] ++ ((Array.range 7).map fun i => s!"worker{i + 1}"))
    assertTrue (view.all (fun node => node.name == ctx.node node.role)) "Dashboard did not use shared pool nodes"⟩,
  ⟨"console.top.all-runs-without-workflow-files", do
    let (_, world) ← checked (command ctx ["top", "--once"])
    for node in actors do assertTrue (has world.stdout node.name) s!"Missing node {node.name}"
    assertTrue (!has world.stdout "demo-blobs") "Infrastructure mixed with actors"
    for metric in ["CPU", "Mem", "Disk", "Net RX", "Net TX", "I/O R", "I/O W"] do
      assertTrue (has world.stdout metric) s!"Missing graph {metric}"
    for machine in ["machine-0", "machine-1", "machine-2", "machine-3"] do
      assertTrue (has world.stdout ("Node " ++ machine)) "Host placement missing from HTTP dashboard"
    for capacity in ["8 logical CPUs", "16.0 GiB RAM", "1.500 CPUs", "512.0 MiB"] do
      assertTrue (has world.stdout capacity) s!"Missing capacity {capacity}"
    assertTrue (!world.trace.contains "enterTerminal" &&
      !world.trace.contains "key" && !world.stdout.contains '\x1b') "Snapshot needed workflow metadata or a TTY"
    assertEq world.httpRequests.size 1⟩,
  ⟨"console.top.paging-and-refresh", do
    let (_, world) ← checked (command ctx ["top"])
      { initial with keys := keys "\x1b[6~\x1b[5~" ++ List.replicate 10 0 ++ [113] }
    assertTrue (has world.stdout "2/2" && has world.stdout "1/2") "Paging did not redraw"
    assertEq world.httpRequests.size 2
    assertTrue (world.keys.isEmpty && !world.terminal) "Top did not quit/restore terminal"
    assertTrue (world.stdout.endsWith "\x1b[?1049l") "Alternate screen not restored"⟩,
  ⟨"console.top.resize-and-no-color", do
    let (_, world) ← checked (command ctx ["top"]) { initial with
      sizes := [(120, 35), (80, 24)], keys := [0, 113], envs := initial.envs.push ("NO_COLOR", "1") }
    assertTrue (has world.stdout "1/2" && has world.stdout "1/8") "Resize did not adjust the grid"
    assertTrue (!has world.stdout "\x1b[0;32m" && !has world.stdout "\x1b[0;30;46m") "Ignored NO_COLOR"⟩,
  ⟨"console.top.non-tty-and-empty-deployment", do
    let (_, world) ← checked (command ctx ["top"]) { initial with terminalAvailable := false }
    assertTrue (!world.stdout.contains '\x1b' && !world.trace.contains "key") "Non-TTY command did not return"
    let (_, world) ← checked (command ctx ["top", "--once"]) (connected #[])
    assertTrue (has world.stdout "No workers or schedulers") "Empty deployment had no explanation"
    assertEq world.httpRequests.size 1 "Empty dashboard requested extra data"⟩,
  ⟨"console.top.missing-metrics-do-not-look-idle", do
    let (_, world) ← checked (command ctx ["top", "--once"])
      (connected (actors.map fun n => { n with resources := none }))
    assertTrue (has world.stdout "Stats: unavailable") "Missing statistics looked like zero usage"
    assertTrue (!has world.stdout "0.00%") "Fabricated zero CPU on missing sample"⟩,
  ⟨"console.top.frame-bounds-and-stale-samples", do
    for width in [0, 5, 39, 40, 80, 110, 120, 180] do
      for height in [0, 5, 13, 14, 24, 35] do
        let view := Top.frame "test" actors 100 width height
        assertTrue (view.size ≤ height - 1 && view.all (·.length ≤ width - 1)) "Dashboard escaped terminal bounds"
    let node := actors[0]!
    let view := Top.frame "test" #[{ node with state := "exited" }] 0 120 35
    assertTrue (view.any (fun line => has line "node is unavailable")) "Stopped node displayed as live"⟩,
  ⟨"console.top.terminal-cleanup-on-error", do
    let (_, success) ← checked (command ctx ["top"])
    for index in [:success.trace.size] do
      if success.trace[index]! == "leaveTerminal" then continue
      let (_, world) := ConsoleModel.run (command ctx ["top"]) { initial with failAt := some index }
      assertTrue (!world.terminal && world.locks.isEmpty)
        s!"Top leaked resources at {index}: {success.trace[index]!}"⟩,
  ⟨"console.top.shell-handoff-and-completion", do
    let (_, world) ← checked (do discard (request .enterTerminal); Shell.run ctx) { initial with keys := keys "top\rqhelp\rquit\r" }
    assertTrue (world.keys.isEmpty && !world.terminal) "Top did not return to anchored shell"
    assertEq (world.trace.filter (· == "enterTerminal")).size 3
    assertEq (world.trace.filter (· == "leaveTerminal")).size 3
    assertTrue (has world.stdout "Commands:" && has world.stdout "I/O W") "Dashboard or subsequent command missing"
    assertEq ((Completion.candidates {} (Completion.context "top --" 6)).map (·.value)) #["--once", "--help"]
    assertEq ((Completion.candidates {} (Completion.context "to" 2)).map (·.value)) #["top"]⟩
]

end LeanCloudTests
