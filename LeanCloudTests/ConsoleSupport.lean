import LeanCloudCli.Console

namespace LeanCloudTests.ConsoleRuntime
open Lean LeanCloud LeanCloudCli

/-- Retained test artifacts must not be discovered by the user's catalog. -/
def isolate (ctx : Context) : Cli Unit := do
  request (.createDir ctx.home)
  saveJson (ctx.home / "catalog-owner.json") (← Deployments.home).toString

def require (condition : Bool) (message : String) : Cli Unit :=
  unless condition do throw message

partial def awaitOutcome (ctx : Context) (run : Run) (deadline : Nat) : Cli Exit := do
  -- Blob volumes may still be registering after the service health check passes.
  let result ← observing (ctx.outcome run)
  if let .ok (some outcome) := result then return outcome
  unless (← request .now) < deadline do
    match result with
    | .error error => throw s!"Console result unavailable: {error}"
    | _ => throw "Console run timed out"
  request (.sleep 250)
  awaitOutcome ctx run deadline

def poolNodes (ctx : Context) : Cli String := do
  let count := (← ctx.deployment).workers
  let actors := (#["scheduler"] ++ workerNames count).map ctx.node
  let states ← docker (#["inspect", "--format", "{{.State.Running}} {{.HostConfig.RestartPolicy.Name}}"] ++ actors)
  require (states.stdout.trimAscii.toString.splitOn "\n" == List.replicate (count + 1) "true unless-stopped")
    "Persistent pool is not running"
  let nodes ← ctx.nodes
  require (nodes.size == count + 2 && nodes.all (fun node => (deploymentServices count).contains node.role))
    "Deployment must contain the configured combined nodes and blob storage"
  for actor in actors do
    discard <| docker #["exec", actor, "cloud-node", "health"]
  let ids ← docker (#["inspect", "--format", "{{.Id}}"] ++ actors)
  return ids.stdout

def cleanup (ctx : Context) : Cli Unit := do
  let nodes ← docker #["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project] false
  let ids := nodes.stdout.splitOn "\n" |>.filter (!·.isEmpty) |>.toArray
  if !ids.isEmpty then discard <| docker (#["rm", "-f"] ++ ids) false
  discard <| ctx.compose #["down", "-v", "--remove-orphans"]
  let count ← try pure (← ctx.deployment).retainedCount catch _ => pure defaultWorkerCount
  for volume in deploymentVolumes count do
    discard <| docker #["volume", "rm", ctx.project ++ "_" ++ volume] false
  let images ← docker #["image", "ls", "--format", "{{.Repository}}:{{.Tag}}", ctx.project ++ "-app"] false
  for tag in images.stdout.splitOn "\n" do
    if tag.startsWith (ctx.project ++ "-app:") then discard <| docker #["image", "rm", tag] false

/-- Capture the combined nodes and blob service before cleanup removes them.
Record only container state, not configuration or credentials. -/
def captureFailure (ctx : Context) : Cli Unit := do
  let save (name : String) (action : Cli ProcessOutput) : Cli Unit := do
    let content ← match ← observing action with
      | .ok output => pure s!"exit={output.exitCode}\n{output.stdout}{output.stderr}"
      | .error error => pure error
    request (.writeFile (ctx.home / s!"failure-{name}.log") content)
  match ← observing ctx.nodes with
  | .error error => request (.writeFile (ctx.home / "failure-inventory.log") error)
  | .ok nodes =>
    for node in nodes do
      save s!"{node.name}-state" (docker #["inspect", "--format", "{{json .State}}", node.name] false)
      save node.name (docker #["logs", "--timestamps", "--tail", "2000", node.name] false)

end LeanCloudTests.ConsoleRuntime
