import LeanCloudRuntime.HttpMailbox
import LeanCloudRuntime.S3

namespace LeanCloudRuntime
open Lean LeanCloud

structure SchedulerConfig where
  database : String := "/data/scheduler.sqlite"
  assignmentMs : Nat := 30000
  deriving FromJson, ToJson

structure Config where
  mailboxes : HttpMailbox.Mailboxes
  scheduler : SchedulerConfig
  blobs : S3.Config
  deriving FromJson, ToJson

def Config.load (path : System.FilePath) : IO Config := do
  let config ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson? (α := Config))
  IO.ofExcept config.mailboxes.validate
  unless config.scheduler.assignmentMs > 0 do throw (IO.userError "Assignment timeout must be positive")
  return config

structure RunDefinition where
  entry : String
  input : Json
  resultSchema : String
  deriving FromJson, ToJson

def validateRun (run : String) : IO Unit :=
  unless !run.isEmpty && run.length ≤ 100 && run.toList.all (fun c =>
      c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_')) do
    throw (IO.userError "Run id must contain 1–100 ASCII letters, digits, '-' or '_'")

/-- Persist the immutable definition before publishing a pool registration. -/
def submit (config : Config) (run : String) (definition : RunDefinition) : IO Unit := do
  validateRun run
  let stored ← S3.createJson config.blobs run "definition" (toJson definition)
  unless stored == toJson definition do
    throw (IO.userError "Run id already belongs to a different workflow or input")

def loadRun (config : Config) (run : String) : IO RunDefinition := do
  let some value ← S3.readJson config.blobs run "definition"
    | throw (IO.userError "Run does not exist; submit it first")
  IO.ofExcept (fromJson? value)

def completed (config : Config) (run : String) : IO (Option Exit) := do
  match ← ((S3.records config.blobs run).outcome).run with
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
