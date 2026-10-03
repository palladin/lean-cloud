import LeanCloudRuntime.LocalDb
import LeanCloudRuntime.RabbitMQ
import LeanCloudRuntime.ProcessLock
import LeanCloudRuntime.S3

namespace LeanCloudRuntime
open Lean LeanCloud

structure SchedulerConfig where
  database : String := "/data/scheduler.sqlite"
  assignmentMs : Nat := 30000
  deriving FromJson, ToJson

structure Config where
  broker : RabbitMQ.Config
  scheduler : SchedulerConfig
  blobs : S3.Config
  deriving FromJson, ToJson

def Config.load (path : System.FilePath) : IO Config := do
  let config ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson? (α := Config))
  unless 0 < config.broker.port && config.broker.port ≤ 65535 do
    throw (IO.userError "RabbitMQ port must be between 1 and 65535")
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

/-- Submitting the same definition is idempotent. Deploy one scheduler for this
run; its initial private state contains the root job. Workers load the immutable
entry point/input from blobs. The scheduler never loads workflow data. -/
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

/-- One durable scheduler mailbox and a private SQLite volume. The same actor
turn as Sim saves state, confirms its outgoing messages, then acknowledges input.
Broker/connection failures terminate the process; restart reopens the mailbox. -/
def runScheduler (config : Config) (run : String) : IO Unit := do
  let lock ← ProcessLock.acquire (config.scheduler.database ++ ".lock")
  try
    let conn ← LeanLinq.Sqlite.connect config.scheduler.database
    try
      LocalDb.initializeSchema conn
      let handle ← RabbitMQ.openMailbox config.broker run "scheduler"
      try
        let store := LocalDb.store conn run
        let inbox : Mailbox IO SchedulerMessage := RabbitMQ.inbox handle
        let lastTime ← IO.mkRef (← IO.monoMsNow)
        let ports : SchedulerPorts IO := {
          localDb := store
          inbox := {
            receive := do
              let now ← IO.monoMsNow
              let elapsed := now - (← lastTime.get)
              if elapsed ≥ 500 then
                lastTime.set now
                return some ⟨0, .tick elapsed⟩
              let delivery ← inbox.receive
              if let some delivery := delivery then
                if let .tick _ := delivery.message then throw (IO.userError "Invalid external timer message")
              return delivery
            acknowledge := fun receipt => if receipt == 0 then pure () else inbox.acknowledge receipt }
          send := fun delivery => RabbitMQ.send config.broker run ("worker." ++ delivery.worker) delivery.message }
        Scheduler.recover store
        IO.println s!"scheduler ready for {run} using RabbitMQ"
        (← IO.getStdout).flush
        repeat Scheduler.turn ports config.scheduler.assignmentMs
      finally handle.close
    finally conn.close
  finally ProcessLock.release lock

private def observe (records : ReplayStore IO) : IO (Worker.ObservedStore IO) := do
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

/-- Stable across container restarts so RabbitMQ redelivers into the same inbox.
On a host running several processes, provide a distinct CLOUD_WORKER_ID for each. -/
private def workerId : IO String := do
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

/-- Workers consume their own durable mailbox. RabbitMQ retains reports and
assignments independently of either actor's process lifetime. -/
def runWorker [Codec α] (config : Config) (run : String)
    (program : ι → Cloud IO α) (input : ι) : IO Unit := do
  let id ← workerId
  let handle ← RabbitMQ.openMailbox config.broker run ("worker." ++ id)
  try
    let inbox : Mailbox IO WorkerMessage := RabbitMQ.inbox handle
    let failure ← IO.mkRef (none : Option CloudError)
    let ports : Worker.Ports IO := {
      id
      inbox := {
        receive := do
          let delivery ← inbox.receive
          if let some delivery := delivery then
            match delivery.message with
            | .execute assignment =>
              IO.println s!"worker {id} attempt={assignment.attempt} location={assignment.location.key}"
              (← IO.getStdout).flush
            | .failed error => failure.set (some error)
            | _ => pure ()
          return delivery
        acknowledge := inbox.acknowledge }
      send := fun message => RabbitMQ.send config.broker run "scheduler" message
      observe := ← observe (S3.records config.blobs run)
      blobs := S3.storage config.blobs }
    IO.println s!"worker {id} joined {run} via RabbitMQ"
    (← IO.getStdout).flush
    let mut state : Worker.State := {}
    repeat
      state ← Worker.turn ports 100000 program input state
      if state.stopped then
        if let some error ← failure.get then throw (IO.userError error.message)
        return
      IO.sleep 50
  finally handle.close

def status (config : Config) (run : String) : IO Scheduler.State := do
  let random ← IO.Process.output { cmd := "openssl", args := #["rand", "-hex", "16"] }
  unless random.exitCode == 0 do throw (IO.userError "Cannot allocate status reply address")
  let id := "status-" ++ random.stdout.trimAscii.toString
  let handle ← RabbitMQ.openMailbox config.broker run ("worker." ++ id)
  try
    let inbox : Mailbox IO WorkerMessage := RabbitMQ.inbox handle
    RabbitMQ.send config.broker run "scheduler" (SchedulerMessage.inspect id)
    let deadline := (← IO.monoMsNow) + 5000
    repeat
      if (← IO.monoMsNow) > deadline then throw (IO.userError "Scheduler status timed out")
      let some delivery ← inbox.receive | continue
      match delivery.message with
      | .status value =>
        let state ← IO.ofExcept (fromJson? value)
        inbox.acknowledge delivery.receipt
        handle.delete
        return state
      | _ => throw (IO.userError "Unexpected scheduler status response")
  finally handle.close

end LeanCloudRuntime
