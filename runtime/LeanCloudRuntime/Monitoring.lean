import LeanCloudRuntime.Pool
import LeanCloudRuntime.ObservationStore

namespace LeanCloudRuntime.Monitoring
open Lean LeanCloud

private def routes (config : Config) : IO (Array HttpMailbox.WorkerEndpoint) := do
  let membership ← Pool.request config .workers
  IO.ofExcept (membership.getObjValAs? _ "routes")

private def call (endpoint : HttpMailbox.Config) (request : DeploymentApi.Request) : IO Json := do
  let response ← LeanCloudCli.Http.post s!"http://{endpoint.host}:{endpoint.port}/telemetry"
    endpoint.token request.encode.compress 1500
  let result : Except String Json ← IO.ofExcept (Json.parse response >>= fromJson?)
  IO.ofExcept result

/-- Private node endpoint. Only diagnostic reads are accepted. -/
def api (store : ObservationStore.Store) (json : Json) : IO Json := do
  match ← IO.ofExcept (DeploymentApi.Request.decode json) with
  | .nodes => return toJson (← store.node)
  | .observations run worker after limit =>
    unless worker == store.worker do throw (IO.userError "Node identity mismatch")
    return toJson (← store.page run after limit)
  | _ => throw (IO.userError "Unsupported telemetry request")

def nodes (config : Config) (store : ObservationStore.Store) : IO (Array DeploymentApi.Node) := do
  let tasks ← (← routes config).mapM fun route => IO.asTask (do
    try
      let node : DeploymentApi.Node ← IO.ofExcept (fromJson? (← call route.endpoint .nodes))
      unless node.id == route.worker do throw (IO.userError "Node identity mismatch")
      return node
    catch _ => return { id := route.worker, online := false, warning := "Node endpoint unavailable" }) .dedicated
  let mut result := #[← store.node]
  for task in tasks do result := result.push (← IO.ofExcept task.get)
  return result

def observations (config : Config) (store : ObservationStore.Store)
    (run worker : String) (after : Option String) (limit : Nat) : IO DeploymentApi.ObservationPage := do
  if worker == "scheduler" then return ← store.page run after limit
  let some route := (← routes config).find? (·.worker == worker)
    | throw (IO.userError "Unknown worker")
  IO.ofExcept (fromJson? (← call route.endpoint (.observations run worker after limit)))

end LeanCloudRuntime.Monitoring
