import LeanCloudCli.Application
import LeanCloudCli.IO

namespace LeanCloudTests.ConsoleRuntime
open Lean LeanCloud LeanCloudCli

def require (condition : Bool) (message : String) : Cli Unit :=
  unless condition do throw message

partial def awaitOutcome (ctx : Context) (run : Run) (deadline : Nat) : Cli Exit := do
  if let some outcome ← ctx.outcome run then return outcome
  require ((← request .now) < deadline) "Workflow did not complete"
  request (.sleep 250)
  awaitOutcome ctx run deadline

/-- A fresh client's host can read only its own directory and cannot run any
process. All application data, source and counters must cross the public API. -/
def remoteClient (directory : System.FilePath) (url token : String) (nodeCount : Nat) : Cli Unit := do
  request (.createDir directory)
  let handler : {α : Type} → HostOp α → Cli (Except String α) := fun op =>
    match op with
    | .getEnv "LEAN_CLOUD_HOME" => pure (.ok (some directory.toString))
    | .getEnv "REMOTE_TEST_TOKEN" => pure (.ok (some token))
    | .currentDir => pure (.ok directory)
    | .readFile path =>
      if path.toString.startsWith (directory.toString ++ "/") then observing (request (.readFile path))
      else pure (.error "Remote client attempted to read the application's files")
    | op => observing (request op)
  let check : Cli Unit := do
    let (ctx, _) ← dispatch ⟨directory, "unconfigured"⟩ ["connect", "fresh", url, "--token-env", "REMOTE_TEST_TOKEN"]
    discard <| command ctx ["run", "sum-squares", "--id", "remote-1"]
    let run ← ctx.loadRun "remote-1"
    let result ← awaitOutcome ctx run ((← request .now) + 90000)
    require (result == .success (toJson (55 : Nat))) "Remote workflow result differs from direct evaluation"
    require (!run.program.sources.isEmpty) "Server did not provide submitted source"
    for args in [["ps"], ["inspect", "remote-1"], ["result", "remote-1"], ["top", "--once"], ["watch", "remote-1", "--once"]] do
      discard <| command ctx args
    let snapshot ← LeanCloudCli.Trace.load ctx run
    require (snapshot.steps.any (·.event.source.isSome)) "Remote source positions are missing"
    require (snapshot.steps.any (·.job.isSome)) "Remote scheduler branches are missing"
    require (snapshot.steps.any fun s => s.resources.any (·.cpuNs.isSome)) "Remote counters are missing"
    let some connection ← ctx.connection | throw "Missing saved connection"
    let nodes ← Client.call connection .nodes
    require (nodes.size == nodeCount && nodes.all (·.online)) "Remote node inventory is incomplete"
    -- Drop every client-side run/source/snapshot cache. A second connection
    -- must still inspect a run completed before this client existed.
    request (.removeTree ctx.home)
    let (fresh, _) ← dispatch ⟨directory, "unconfigured"⟩ ["connect", "fresh", url, "--token-env", "REMOTE_TEST_TOKEN"]
    discard <| command fresh ["watch", "remote-1", "--once"]
    let final ← LeanCloudCli.Trace.load fresh (← fresh.loadRun "remote-1")
    require (final.steps.any (·.event.source.isSome)) "Final source depended on a prior client cache"
    discard <| command fresh ["remove", "remote-1"]
    require (!(← fresh.allRuns).any (·.id == "remote-1")) "Removed run remained in remote catalog"
    -- The same suite checks real user blob effects and workflow controls on any
    -- deployment. Provisioning and node restarts remain outside the client.
    let programs ← fresh.deployment
    let some program := programs.programs.find? (·.entry == "log-summary/v1")
      | throw "No log-summary example"
    let some input := program.sampleInput | throw "No log-summary sample input"
    let inputFile := directory / "input.json"
    saveJson inputFile (input.setObjVal! "pauseMs" (toJson (1500 : Nat)))
    for (id, action) in [("remote-paused", "pause"), ("remote-killed", "kill")] do
      discard <| command fresh ["run", "log-summary", "--input", inputFile.toString, "--id", id]
      discard <| command fresh [action, id]
    let killed ← awaitOutcome fresh (← fresh.loadRun "remote-killed") ((← request .now) + 120000)
    require (match killed with | .cancelled _ => true | _ => false) "Kill did not publish cancellation"
    let paused ← fresh.loadRun "remote-paused"
    require ((← fresh.control paused.id) == .paused && (← fresh.outcome paused).isNone)
      "Paused workflow did not remain paused"
    discard <| command fresh ["resume", paused.id]
    let resumed ← awaitOutcome fresh paused ((← request .now) + 120000)
    require (match resumed with | .success _ => true | _ => false) "Resumed blob workflow failed"
    require ((← fresh.result paused) == "files=16, errors=24\n") "Remote blob result differs from expected"
    for id in ["remote-paused", "remote-killed"] do discard <| command fresh ["remove", id]
  liftExcept (← Cli.runWith handler check)
  printLine "Fresh remote client passed: submit, blobs, pause/resume/kill, result, catalog, source, live nodes, last view, and removal without Docker or a checkout."

end LeanCloudTests.ConsoleRuntime
