import LeanCloudTests.ConsoleSupport
import LeanCloudTests.PoolWorkload

namespace LeanCloudTests.ConsoleRuntime
open Lean LeanCloud LeanCloudCli

private def chaosEvent (ctx : Context) (kind : String) (fields : List (String × Json) := []) : Cli Unit := do
  let event := Json.mkObj (("timeMs", toJson (← request .now)) :: ("event", toJson kind) :: fields)
  request (.appendFile (ctx.home / "chaos-events.jsonl") (event.compress ++ "\n"))
  printLine (Json.mkObj (("event", toJson kind) :: fields.filter (·.1 != "runs"))).compress

private def healthy (ctx : Context) (role : String) : Cli Unit := do
  let deadline := (← request .now) + 90000
  repeat
    let health ← docker #["exec", ctx.node role, "cloud-node", "health"] false
    if health.exitCode == 0 then return
    require ((← request .now) < deadline) s!"{role} did not recover HTTP and its actor"
    request (.sleep 250)

private def states (ctx : Context) (runs : Array Run) : Cli (Array Scheduler.State) :=
  runs.mapM ctx.scheduler

/-- Wait for reported assignments rather than injecting faults into an idle pool.
The pre-kill snapshot is evidence of activity, not an exact instruction boundary. -/
private def busy (ctx : Context) (runs : Array Run) (completedBranches : Nat) (overlap : Bool) :
    Cli (Array Scheduler.State × Array String) := do
  let deadline := (← request .now) + 60000
  repeat
    let snapshots ← states ctx runs
    let workers := snapshots.foldl (fun workers state => state.jobs.foldl (fun workers job =>
      match job.status with
      | .running worker _ _ => if workers.contains worker then workers else workers.push worker
      | _ => workers) workers) (#[] : Array String)
    let active := snapshots.filter (!·.finished)
    let completed := snapshots.foldl (fun n state => n + (state.jobs.filter (·.status == .done)).size) 0
    if !workers.isEmpty && completed ≥ completedBranches &&
        (!overlap || (active.size ≥ 2 && active.all (·.jobs.size > 1))) then
      return (snapshots, workers)
    require (!active.isEmpty) "Chaos missed active work: all workflows already finished"
    require ((← request .now) < deadline) "No active assignments available for fault injection"
    request (.sleep 100)

private def settled (ctx : Context) (runs : Array Run) (deadline : Nat) : Cli Unit := do
  repeat
    let snapshots ← states ctx runs
    if snapshots.all (·.finished) then return
    require ((← request .now) < deadline) "Durable results exist but scheduler did not finish"
    request (.sleep 250)

private def crashNode (ctx : Context) (role : String) : Cli Unit := do
  let before ← docker #["inspect", "--format", "{{.State.StartedAt}}", ctx.node role]
  discard <| docker #["kill", "--signal", "KILL", ctx.node role]
  let killed ← docker #["inspect", "--format", "{{.State.Running}} {{.State.ExitCode}}", ctx.node role]
  require (killed.stdout.trimAscii.toString == "false 137") s!"{role} was not observed exiting from SIGKILL"
  chaosEvent ctx "killed" [("node", toJson role), ("exitCode", toJson (137 : Nat))]
  discard <| docker #["start", ctx.node role]
  healthy ctx role
  let after ← docker #["inspect", "--format", "{{.State.StartedAt}}", ctx.node role]
  require (after.stdout != before.stdout) s!"{role} did not restart"
  chaosEvent ctx "restarted" [("node", toJson role)]

private def chaosFixture (owner : Context) : Cli Context := do
  let directory := owner.home / "application"
  Project.init owner directory.toString (some owner.root.toString)
  let ctx : Context := ⟨directory, owner.project⟩
  isolate ctx
  -- The test fixture is compiled into a normal application, not the demo registry.
  request (.createDir (directory / "ChaosFixture"))
  request (.appendFile (directory / "lakefile.lean") "\nlean_lib ChaosFixture\n")
  request (.writeFile (directory / "ChaosFixture/GeneratedProgram.lean") (include_str "GeneratedProgram.lean"))
  request (.writeFile (directory / "ChaosFixture/PoolWorkload.lean")
    ((include_str "PoolWorkload.lean").replace "import LeanCloudTests.GeneratedProgram" "import ChaosFixture.GeneratedProgram"))
  request (.writeFile (directory / "Main.lean") (include_str "Fixtures/PoolChaosMain.lean.in"))
  return ctx

/-- Generate the exact test application for a separately timed CI image build.
The subsequent suite still executes the normal deploy command. -/
def prepareChaosImage : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let ctx ← chaosFixture ⟨root, "ci-chaos"⟩
  Project.prepare ctx

/-- Run the generated pure workloads through the ordinary CLI deployment,
registry, combined HTTP/SQLite nodes, shared pool and S3 record store. -/
def poolChaos (seed : Nat := 1) : Cli Unit := do
  let root ← request (.realPath (← request .currentDir))
  let ctx ← chaosFixture ⟨root, s!"lean-cloud-pool-chaos-test-{← request .pid}"⟩
  let inputs := PoolWorkload.inputs seed
  let faults := PoolWorkload.plan seed
  saveJson (ctx.home / "chaos-plan.json") (Json.mkObj [
    ("generator", toJson "pool-chaos/v1"), ("seed", toJson seed), ("faults", toJson faults),
    ("programs", toJson (inputs.map fun input => Json.mkObj [
      ("input", toJson input), ("tree", toJson (reprStr (PoolWorkload.tree input))),
      ("expected", toJson (PoolWorkload.expected input))]))])
  printLine s!"Pool chaos seed={seed}; artifacts: {ctx.home}"
  try
    ctx.deploy (workers := some 3)
    let identities ← poolNodes ctx
    let mut runs := #[]
    for i in [:inputs.size] do
      let file := ctx.home / s!"input-{i}.json"
      saveJson file inputs[i]!
      let id := s!"generated-{i}"
      ctx.launch "generated" (some file.toString) (some id)
      runs := runs.push (← ctx.loadRun id)
    for i in [:faults.size] do
      let fault := faults[i]!
      request (.sleep fault.delayMs.toUInt32)
      let (snapshots, workers) ← busy ctx runs fault.completedBranches (i == 0)
      let role := if fault.scheduler then "scheduler" else workers[fault.workerOffset % workers.size]!
      chaosEvent ctx "inject" [("index", toJson i), ("node", toJson role),
        ("runs", toJson (runs.zip snapshots |>.map fun (run, state) =>
          Json.mkObj [("id", toJson run.id), ("state", toJson state)]))]
      crashNode ctx role
    chaosEvent ctx "faults-stopped"
    let deadline := (← request .now) + 300000
    for (run, input) in runs.zip inputs do
      let actual ← awaitOutcome ctx run deadline
      let expected := PoolWorkload.expected input
      chaosEvent ctx "result" [("run", toJson run.id), ("actual", toJson actual), ("expected", toJson expected)]
      require (actual == expected) s!"seed={seed}, run={run.id}: direct/replay mismatch"
    -- Wait for the scheduler to consume the final reports as well as the root writes.
    settled ctx runs deadline
    -- Completed outcomes must survive another scheduler restart and stale delivery.
    crashNode ctx "scheduler"
    for (run, input) in runs.zip inputs do
      require ((← awaitOutcome ctx run deadline) == PoolWorkload.expected input)
        s!"Completed result changed after restart: {run.id}"
    settled ctx runs deadline
    require ((← poolNodes ctx) == identities) "Recovery replaced deployed nodes"
    chaosEvent ctx "passed" [("seed", toJson seed), ("crashes", toJson faults.size)]
    printLine "Pool chaos passed: concurrent generated workflows, scheduler/worker crashes, direct outcomes, and durable recovery."
  catch error =>
    discard <| observing (chaosEvent ctx "failed" [("error", toJson error)])
    discard <| observing (captureFailure ctx)
    throw s!"Pool chaos seed={seed}: {error}\nArtifacts: {ctx.home}"
  finally cleanup ctx

end LeanCloudTests.ConsoleRuntime
