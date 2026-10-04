import LeanCloud.Pool
import LeanCloudRuntime.Run

namespace LeanCloudRuntime.Pool
open Lean LeanCloud

/-- Versioned mailbox namespace, shared by every process in this deployment. -/
def address := "pool-v1"

structure Saved where
  state : LeanCloud.Pool.State := {}
  replies : Array (String × Except String Json) := #[]
  deriving ToJson, FromJson

/-- One request/reply exchange. Each call owns a unique reply address. The
scheduler caches administrative replies before acknowledging requests. -/
def request (config : Config) (command : LeanCloud.Pool.Command) : IO Json := do
  let random ← IO.Process.output { cmd := "openssl", args := #["rand", "-hex", "16"] }
  unless random.exitCode == 0 do throw (IO.userError "Cannot allocate reply address")
  let replyTo := "reply-" ++ random.stdout.trimAscii.toString
  let handle ← RabbitMQ.openMailbox config.mailboxes.scheduler address replyTo
  try
    let inbox : Mailbox IO (Except String Json) := RabbitMQ.inbox handle
    RabbitMQ.send config.mailboxes.scheduler address "scheduler"
      (LeanCloud.Pool.Message.request replyTo command)
    let deadline := (← IO.monoMsNow) + 30000
    repeat
      if (← IO.monoMsNow) > deadline then throw (IO.userError "Deployment scheduler request timed out")
      let some delivery ← inbox.receive | continue
      inbox.acknowledge delivery.receipt
      handle.delete
      return ← IO.ofExcept delivery.message
  finally handle.close

private def settle (config : Config) (command : LeanCloud.Pool.Command) : IO Unit := do
  if let .kill run := command then discard (LeanCloudRuntime.cancel config run)

/-- Sole owner of the deployment's SQLite database. State is durable before
outgoing confirmations, which precede the input acknowledgement. -/
def scheduler (config : Config) : IO Unit := do
  let lock ← ProcessLock.acquire (config.scheduler.database ++ ".lock")
  try
    let conn ← LeanLinq.Sqlite.connect config.scheduler.database
    try
      LocalDb.initializeSchema conn
      let mut saved : Saved ← LocalDb.loadValue conn "pool-v1" {}
      saved := { saved with state := LeanCloud.Pool.recover saved.state }
      LocalDb.saveValue conn "pool-v1" saved
      for run in saved.state.runs do
        if run.mode == .killed then discard (LeanCloudRuntime.cancel config run.id)
      let handle ← RabbitMQ.openMailbox config.mailboxes.scheduler address "scheduler"
      try
        let inbox : Mailbox IO LeanCloud.Pool.Message := RabbitMQ.inbox handle
        let mut lastTime ← IO.monoMsNow
        IO.println "deployment scheduler ready"
        (← IO.getStdout).flush
        repeat
          let now ← IO.monoMsNow
          saved := { saved with state := LeanCloud.Pool.tick (now - lastTime) saved.state }
          lastTime := now
          let some delivery ← inbox.receive | continue
          match delivery.message with
          | .submit run =>
            let (state, _) ← IO.ofExcept (LeanCloud.Pool.command saved.state (.submit run))
            saved := { saved with state }
            LocalDb.saveValue conn "pool-v1" saved
          | .ready worker =>
            let broker ← IO.ofExcept (config.mailboxes.worker worker)
            let (state, reply) := LeanCloud.Pool.acquire config.scheduler.assignmentMs saved.state worker
            saved := { saved with state }
            LocalDb.saveValue conn "pool-v1" saved
            RabbitMQ.send broker address ("worker." ++ worker) reply
            if let .execute run assignment := reply then
              let trace ← Trace.create "scheduler" run
              trace.assign assignment
              trace.emit "dispatch" worker
          | .report run report =>
            let broker ← IO.ofExcept (config.mailboxes.worker report.worker)
            saved := { saved with state := LeanCloud.Pool.report saved.state run report }
            LocalDb.saveValue conn "pool-v1" saved
            RabbitMQ.send broker address ("worker." ++ report.worker) LeanCloud.Pool.Reply.acknowledged
            (← Trace.create "scheduler" run).emit "report" report.worker
          | .request replyTo command =>
            let cached := saved.replies.find? (·.1 == replyTo)
            let (state, response) := match cached with
              | some (_, response) => (saved.state, response)
              | none => match LeanCloud.Pool.command saved.state command with
                | .ok (state, response) => (state, .ok response)
                | .error error => (saved.state, .error error)
            saved := { saved with state }
            let cache := match command with | .check .. | .status .. | .health => false | _ => true
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
  RabbitMQ.send config.mailboxes.scheduler address "scheduler" (LeanCloud.Pool.Message.submit run)

def status (config : Config) (run : String) : IO Scheduler.State := do
  IO.ofExcept (fromJson? (← request config (.status run)))

end LeanCloudRuntime.Pool
