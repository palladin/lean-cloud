import LeanCloudCli.Profiles

namespace LeanCloudCli.Connections
open Lean LeanCloud

/-- A connection's directory is only a CLI cache, not an application checkout. -/
def connect (name url : String) (tokenEnv := "LEAN_CLOUD_TOKEN")
    (tokenFile : Option String := none) : Cli Context := do
  validateId name
  unless name == name.toLower do throw "Connection name must be lowercase"
  let connection ← Client.connect url tokenEnv tokenFile
  let directory ← Profiles.home
  let root := directory / "connections"
  let ctx : Context := ⟨root, name⟩
  request (.createDir root)
  Profiles.checkOwnership ctx
  if let some existing ← ctx.connection then
    unless existing.deployment == connection.deployment do
      throw "This connection name belongs to another deployment; use a different name"
  request (.createDir ctx.home)
  saveJson (ctx.home / "connection.json") connection
  Profiles.remember ctx
  return ctx

private def sameControl (a b : DeploymentApi.Request) : Bool :=
  match a, b with
  | .control _ run action, .control _ other next => run == other && action == next
  | .remove _ run, .remove _ other => run == other
  | _, _ => false

/-- Save identity before sending. An ambiguous failure keeps it for the next
attempt, while a definite server response retires it. Conflicting commands wait
until the uncertain command is resolved, rather than losing its identity. -/
def control (ctx : Context) (connection : Client.Connection) (id : String)
    (make : String → DeploymentApi.Request) : Cli Unit := do
  validateId id
  let directory := ctx.directory id
  request (.createDir directory)
  withLock (directory / "control.lock") do
    let path := directory / "pending-control.json"
    let desired := make "pending"
    let operation ← if ← request (.exists path) then do
        let saved ← readJson (α := DeploymentApi.Request) path
        unless sameControl saved desired do
          throw "A previous control request has an uncertain result. Repeat that command first to resolve it."
        pure saved
      else do
        let operation := make (← request .randomId)
        liftExcept operation.validate
        saveJson path operation
        pure operation
    match operation with
    | .control key run action =>
      let result ← liftExcept (← Client.exchange connection (.control key run action))
      request (.removeTree path)
      liftExcept result
    | .remove key run =>
      let result ← liftExcept (← Client.exchange connection (.remove key run))
      request (.removeTree path)
      liftExcept result
    | _ => throw "Invalid saved control request"

def cachedRun (info : DeploymentApi.RunInfo) : Run := {
  id := info.id, image := info.image.getD ""
  input := info.input
  program := info.program.getD {
    entry := info.entry, inputSchema := "", resultSchema := info.resultSchema
    description := "", sampleInput := none } }

end LeanCloudCli.Connections
