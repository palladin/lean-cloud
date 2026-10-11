import LeanCloudRuntime.HttpMailbox
import LeanCloudRuntime.Storage
import LeanCloud.ExecutionConfig
import LeanCloud.DeploymentApi

namespace LeanCloudRuntime
open Lean LeanCloud

structure SchedulerConfig where
  database : String := "/data/scheduler.sqlite"
  assignmentMs : Nat := 30000
  deriving FromJson, ToJson

/-- Public deployment access is separate from private mailbox credentials.
Cloud provisioners inject these values; old local configurations omit them. -/
abbrev ClientConfig := DeploymentApi.Access

structure Config where
  mailboxes : HttpMailbox.Mailboxes
  scheduler : SchedulerConfig
  blobs : Storage.Config
  worker : ExecutionConfig := {}
  client : Option ClientConfig := none

def Config.objects (config : Config) : ObjectStore := config.blobs.objects

/-- The actor and its inbox share a process. Self-delivery uses loopback, so
startup does not depend on service routing or DNS propagation. Peer routes and
the externally advertised configuration remain unchanged. -/
def Config.localInbox (config : Config) (worker : Option WorkerId) : Config :=
  match worker with
  | none => { config with mailboxes.scheduler.host := "127.0.0.1" }
  | some worker => { config with mailboxes.workers := config.mailboxes.workers.map fun route =>
      if route.worker == worker then { route with endpoint.host := "127.0.0.1" } else route }

instance : ToJson Config where
  toJson value := Version.stamp "formatVersion" (Json.mkObj [
    ("mailboxes", toJson value.mailboxes), ("scheduler", toJson value.scheduler),
    ("blobs", toJson value.blobs), ("worker", toJson value.worker), ("client", toJson value.client)])

instance : FromJson Config where
  fromJson? json := do
    Version.check "formatVersion" "runtime configuration" json
    let object ← json.getObj?
    let worker ← match object["worker"]? with
      | none => pure ({} : ExecutionConfig)
      | some value => fromJson? value
    return {
      mailboxes := ← json.getObjValAs? _ "mailboxes"
      scheduler := ← json.getObjValAs? _ "scheduler"
      blobs := ← json.getObjValAs? _ "blobs"
      worker
      client := ← match object["client"]? with
        | none => pure none
        | some value => fromJson? value }

def Config.validate (config : Config) : Except String Unit := do
  config.mailboxes.validate
  config.blobs.validate
  unless config.scheduler.assignmentMs > 0 do throw "Assignment timeout must be positive"
  config.worker.validate
  if let some client := config.client then
    unless DeploymentApi.validId client.deployment && !client.image.isEmpty do
      throw "Deployment API requires an identity and an application image"
    unless !client.token.isEmpty && !client.token.contains '\r' && !client.token.contains '\n' do
      throw "Invalid deployment API token"
    if client.token == config.mailboxes.scheduler.token ||
        config.mailboxes.workers.any (·.endpoint.token == client.token) then
      throw "Deployment API token must differ from internal mailbox tokens"

def Config.load (path : System.FilePath) : IO Config := do
  let config ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson? (α := Config))
  IO.ofExcept config.validate
  return config

structure RunDefinition where
  entry : String
  input : Json
  resultSchema : String
  image : Option String := none
  program : Option ProgramInfo := none
  deriving ToJson

instance : FromJson RunDefinition where
  fromJson? json := do
    return {
      entry := ← json.getObjValAs? _ "entry"
      input := ← json.getObjVal? "input"
      resultSchema := ← json.getObjValAs? _ "resultSchema"
      image := ← match json.getObjVal? "image" with
        | .error _ => pure none | .ok value => fromJson? value
      program := ← match json.getObjVal? "program" with
        | .error _ => pure none | .ok value => fromJson? value }

/-- Metadata is immutable once saved. Legacy definitions remain readable without
inventing a release identity or substituting today's source for the old code. -/
def RunDefinition.sameSubmission (saved proposed : RunDefinition) : Bool :=
  saved.entry == proposed.entry && saved.input == proposed.input && saved.resultSchema == proposed.resultSchema &&
    saved.image.all (fun image => proposed.image == some image)

def validateRun (run : String) : IO Unit :=
  unless !run.isEmpty && run.length ≤ 100 && run.toList.all (fun c =>
      c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_')) do
    throw (IO.userError "Run id must contain 1–100 ASCII letters, digits, '-' or '_'")

/-- Persist the immutable definition before publishing a pool registration. -/
def submit (config : Config) (run : String) (definition : RunDefinition) : IO Unit := do
  validateRun run
  let stored ← config.objects.createJson run "definition" (toJson definition)
  let saved : RunDefinition ← IO.ofExcept (fromJson? stored)
  unless saved.sameSubmission definition do
    throw (IO.userError "Run id already belongs to a different workflow or input")

def loadRun (config : Config) (run : String) : IO RunDefinition := do
  let some value ← config.objects.readJson run "definition"
    | throw (IO.userError "Run does not exist; submit it first")
  IO.ofExcept (fromJson? value)

def completed (config : Config) (run : String) : IO (Option Exit) := do
  match ← ((config.objects.records run).outcome).run with
  | .ok outcome => return outcome
  | .error error => throw (IO.userError (reprStr error))

def observe (records : ReplayStore IO) : IO (Worker.ObservedStore IO) := do
  let keys ← IO.mkRef (#[] : Array String)
  let note (key : String) := keys.modify fun found => if found.contains key then found else found.push key
  return {
    records := {
      read := fun key => do
        let value ← records.read key
        if value.isSome then note key
        return value
      create := fun key record => do
        let value ← records.create key record
        note key
        return value }
    confirmed := keys.get }

/-- Stable across container restarts so HttpMailbox redelivers into the same inbox.
On a host running several processes, provide a distinct CLOUD_WORKER_ID for each. -/
def workerId : IO String := do
  let id ← match ← IO.getEnv "CLOUD_WORKER_ID" with
    | some id => pure id
    | none => do
      let some hostname ← IO.getEnv "HOSTNAME"
        | throw (IO.userError "Set CLOUD_WORKER_ID to a stable, unique worker address")
      pure hostname
  unless !id.isEmpty && id.length ≤ 64 && id.toList.all (fun c =>
      c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_')) do
    throw (IO.userError "Worker id must contain 1–64 ASCII letters, digits, '-' or '_'")
  return id

end LeanCloudRuntime
