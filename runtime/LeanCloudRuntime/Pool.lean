import LeanCloud.Pool
import LeanCloudRuntime.Run

namespace LeanCloudRuntime.Pool
open Lean LeanCloud

/-- Versioned mailbox namespace, shared by every process in this deployment. -/
def address := "pool-v1"

structure Saved where
  state : LeanCloud.Pool.State := {}
  routes : Option (Array RabbitMQ.WorkerBroker) := none
  replies : Array (String × Except String Json) := #[]
  deriving ToJson, FromJson

inductive Envelope where
  | event (message : LeanCloud.Pool.Message)
  | configure (replyTo : String) (routes : Array RabbitMQ.WorkerBroker)
  deriving ToJson, FromJson

-- Accept queued messages from the previous wire format during an upgrade.
private structure Incoming where
  envelope : Envelope

private instance : FromJson Incoming where
  fromJson? json := do
    match fromJson? (α := Envelope) json with
    | .ok envelope => return ⟨envelope⟩
    | .error _ => return ⟨.event (← fromJson? json)⟩

def send (config : Config) (message : LeanCloud.Pool.Message) : IO Unit :=
  RabbitMQ.send config.mailboxes.scheduler address "scheduler" (Envelope.event message)

/-- One request/reply exchange. Each call owns a unique reply address. The
scheduler caches administrative replies before acknowledging requests. -/
private def exchange (config : Config) (message : String → Envelope) : IO Json := do
  let random ← IO.Process.output { cmd := "openssl", args := #["rand", "-hex", "16"] }
  unless random.exitCode == 0 do throw (IO.userError "Cannot allocate reply address")
  let replyTo := "reply-" ++ random.stdout.trimAscii.toString
  let handle ← RabbitMQ.openMailbox config.mailboxes.scheduler address replyTo
  try
    let inbox : Mailbox IO (Except String Json) := RabbitMQ.inbox handle
    RabbitMQ.send config.mailboxes.scheduler address "scheduler"
      (message replyTo)
    let deadline := (← IO.monoMsNow) + 30000
    repeat
      if (← IO.monoMsNow) > deadline then throw (IO.userError "Deployment scheduler request timed out")
      let some delivery ← inbox.receive | continue
      inbox.acknowledge delivery.receipt
      handle.delete
      return ← IO.ofExcept delivery.message
  finally handle.close

def request (config : Config) (command : LeanCloud.Pool.Command) : IO Json :=
  exchange config (fun replyTo => .event (.request replyTo command))

def configure (config : Config) (routes : Array RabbitMQ.WorkerBroker) : IO Json := do
  IO.ofExcept ({ config.mailboxes with workers := routes }.validate)
  exchange config (fun replyTo => .configure replyTo routes)

private def reconfigure (config : Config) (saved : Saved)
    (routes : Array RabbitMQ.WorkerBroker) : Except String Saved := do
  ({ config.mailboxes with workers := routes } : RabbitMQ.Mailboxes).validate
  let (state, _) ← LeanCloud.Pool.command saved.state (.configureWorkers (routes.map (·.worker)))
  let retained := saved.routes.getD config.mailboxes.workers
  let retained := routes.foldl (fun all route =>
    (all.filter (·.worker != route.worker)).push route) retained
  return { saved with state, routes := some retained }

private def settle (config : Config) (command : LeanCloud.Pool.Command) : IO Unit := do
  if let .kill run := command then discard (LeanCloudRuntime.cancel config run)

/-- An offline worker must not block pool administration. Its assignment/report
is already durable. Workers repeat readiness and recover the same assignment;
report acknowledgements carry no state needed by the worker. -/
private def reply (broker : RabbitMQ.Config) (worker : String) (message : LeanCloud.Pool.Reply) : IO Unit := do
  try RabbitMQ.send broker address ("worker." ++ worker) message
  catch _ => IO.eprintln s!"Mailbox for {worker} unavailable; waiting for worker readiness."

/-- Sole owner of the deployment's SQLite database. State is durable before
replies and input acknowledgements. Administrative replies use confirmed delivery;
an offline worker recovers its reply by repeating readiness. -/
def scheduler (config : Config) : IO Unit := do
  let lock ← ProcessLock.acquire (config.scheduler.database ++ ".lock")
  try
    let conn ← LeanLinq.Sqlite.connect config.scheduler.database
    try
      LocalDb.initializeSchema conn
      let mut saved : Saved ← LocalDb.loadValue conn "pool-v1" {}
      if saved.routes.isNone then
        saved ← IO.ofExcept (reconfigure config saved config.mailboxes.workers)
      saved := { saved with state := LeanCloud.Pool.recover saved.state }
      LocalDb.saveValue conn "pool-v1" saved
      for run in saved.state.runs do
        if run.mode == .killed then discard (LeanCloudRuntime.cancel config run.id)
      let handle ← RabbitMQ.openMailbox config.mailboxes.scheduler address "scheduler"
      try
        let inbox : Mailbox IO Incoming := RabbitMQ.inbox handle
        let mut lastTime ← IO.monoMsNow
        IO.println "deployment scheduler ready"
        (← IO.getStdout).flush
        repeat
          let now ← IO.monoMsNow
          saved := { saved with state := LeanCloud.Pool.tick (now - lastTime) saved.state }
          lastTime := now
          let some delivery ← inbox.receive | continue
          match delivery.message.envelope with
          | .configure replyTo routes =>
            let cached := saved.replies.find? (·.1 == replyTo)
            let (updated, response) := match cached with
              | some (_, response) => (saved, response)
              | none => match reconfigure config saved routes with
                | .error error => (saved, .error error)
                | .ok updated => (updated, .ok Json.null)
            saved := updated
            if cached.isNone then
              saved := { saved with replies := saved.replies.push (replyTo, response) }
              LocalDb.saveValue conn "pool-v1" saved
            RabbitMQ.send config.mailboxes.scheduler address replyTo response
          | .event message =>
            let mailboxes := { config.mailboxes with workers := saved.routes.getD config.mailboxes.workers }
            match message with
            | .submit run =>
              let (state, _) ← IO.ofExcept (LeanCloud.Pool.command saved.state (.submit run))
              saved := { saved with state }
              LocalDb.saveValue conn "pool-v1" saved
            | .ready worker =>
              unless saved.state.membership.drained.contains worker do
              if let .ok broker := mailboxes.worker worker then
                let (state, reply) := LeanCloud.Pool.acquire config.scheduler.assignmentMs saved.state worker
                saved := { saved with state }
                LocalDb.saveValue conn "pool-v1" saved
                LeanCloudRuntime.Pool.reply broker worker reply
                if let .execute run assignment := reply then
                  let trace ← Trace.create "scheduler" run
                  trace.assign assignment
                  trace.emit "dispatch" worker
            | .drained worker generation =>
              saved := { saved with state := LeanCloud.Pool.drained saved.state worker generation }
              LocalDb.saveValue conn "pool-v1" saved
            | .report run report =>
              unless saved.state.membership.drained.contains report.worker do
              if let .ok broker := mailboxes.worker report.worker then
                saved := { saved with state := LeanCloud.Pool.report saved.state run report }
                LocalDb.saveValue conn "pool-v1" saved
                reply broker report.worker .acknowledged
                (← Trace.create "scheduler" run).emit "report" report.worker
            | .request replyTo command =>
              let cached := saved.replies.find? (·.1 == replyTo)
              let (state, response) := match cached with
                | some (_, response) => (saved.state, response)
                | none => match LeanCloud.Pool.command saved.state command with
                  | .ok (state, response) => (state, .ok response)
                  | .error error => (saved.state, .error error)
              saved := { saved with state }
              let cache := match command with | .check .. | .status .. | .health | .workers => false | _ => true
              if cache && cached.isNone then
                saved := { saved with replies := saved.replies.push (replyTo, response) }
              if cache then LocalDb.saveValue conn "pool-v1" saved
              if response.isOk then
                settle config command
                match command with
                | .pause run => (← Trace.create "scheduler" run).emit "paused" ""
                | .resume run => (← Trace.create "scheduler" run).emit "resumed" ""
                | .kill run => (← Trace.create "scheduler" run).emit "sealed" ""
                | _ => pure ()
              RabbitMQ.send config.mailboxes.scheduler address replyTo response
          inbox.acknowledge delivery.receipt
      finally handle.close
    finally conn.close
  finally ProcessLock.release lock

/-- Registration follows immutable definition persistence. A retried submission
cannot replace the program/input or reactivate a paused/killed process. -/
def submit (config : Config) (run : String) : IO Unit := do
  send config (.submit run)

def status (config : Config) (run : String) : IO Scheduler.State := do
  IO.ofExcept (fromJson? (← request config (.status run)))

end LeanCloudRuntime.Pool
