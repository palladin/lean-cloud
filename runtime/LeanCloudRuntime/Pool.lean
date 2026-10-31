import LeanCloud.Pool
import LeanCloud.Timing
import LeanCloud.ControlReceipts
import Std.Time.DateTime.Timestamp
import LeanCloudRuntime.Run
import LeanCloudRuntime.LocalDb
import LeanCloudRuntime.ProcessLock
import LeanCloudRuntime.Trace

namespace LeanCloudRuntime.Pool
open Lean LeanCloud

/-- Versioned mailbox namespace, shared by every process in this deployment. -/
def address := "pool-v1"

structure Saved where
  state : LeanCloud.Pool.State := {}
  routes : Option (Array HttpMailbox.WorkerEndpoint) := none
  replies : Array (String × Except String Json) := #[]
  timings : Array (String × Timing.Run) := #[]
  receipts : Array ControlReceipts.Receipt := #[]

/-- Persist the catalog and administrative intent, not the scheduling tree,
tickets, leases or continuations. Attempt counters fence delayed old mail. -/
instance : ToJson Saved where
  toJson saved := Json.mkObj [
    ("formatVersion", toJson Version.current),
    ("state", toJson saved.state.catalog),
    ("routes", toJson saved.routes), ("replies", toJson saved.replies), ("timings", toJson saved.timings),
    ("receipts", toJson saved.receipts)]

instance : FromJson Saved where
  fromJson? json := do
    Version.check "formatVersion" "scheduler catalog" json
    return { state := (← json.getObjValAs? LeanCloud.Pool.Catalog "state").restore
             routes := ← json.getObjValAs? _ "routes"
             replies := ← json.getObjValAs? _ "replies"
             timings := ← json.getObjValAs? _ "timings"
             receipts := ← json.getObjValAs? _ "receipts" }

private def wallTime : IO Nat := do
  return (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val.toNat

inductive Envelope where
  | event (message : LeanCloud.Pool.Message)
  | configure (replyTo : String) (routes : Array HttpMailbox.WorkerEndpoint)
  | control (replyTo requestId : String) (command : LeanCloud.Pool.Command)
  deriving ToJson, FromJson

def send (config : Config) (message : LeanCloud.Pool.Message) : IO Unit :=
  HttpMailbox.send config.mailboxes.scheduler address "scheduler" (Envelope.event message)

/-- Keep the work lease alive independently of user computation. The action
checks transport failure at record boundaries; closing always joins the task.
The scheduler still checks the attempt before accepting renewals or reports. -/
def withHeartbeat (config : Config) (run worker : String) (attempt : Nat)
    (action : IO Unit → IO α) : IO α := do
  let stopped ← IO.mkRef false
  let failure ← IO.mkRef (none : Option IO.Error)
  let interval := max 1 (config.scheduler.assignmentMs / 3)
  let heartbeat ← IO.asTask (do
    let mut next ← IO.monoMsNow
    while !(← stopped.get) do
      if (← IO.monoMsNow) ≥ next then
        try
          send config (.renew run worker attempt)
          next := (← IO.monoMsNow) + interval
        catch error => failure.set (some error); return
      IO.sleep (min 50 interval).toUInt32) .dedicated
  try
    action (do if let some error ← failure.get then throw error)
  finally
    stopped.set true
    discard <| IO.ofExcept heartbeat.get

/-- One request/reply exchange. A timeout is ambiguous: the command may already
be committed. Its retired reply address cannot be reused to execute it again. -/
private def exchange (config : Config) (message : String → Envelope) : IO (Except String Json) := do
  let handle ← HttpMailbox.openReply config.mailboxes.scheduler
  try
    let inbox : Mailbox IO (Except String Json) := HttpMailbox.inbox handle
    HttpMailbox.send config.mailboxes.scheduler address "scheduler"
      (message handle.queue)
    let deadline := (← IO.monoMsNow) + 30000
    repeat
      if (← IO.monoMsNow) > deadline then
        throw (IO.userError "Deployment scheduler request timed out; the command may already have completed")
      let some delivery ← inbox.receive | continue
      inbox.acknowledge delivery.receipt
      return delivery.message
  finally handle.close

def request (config : Config) (command : LeanCloud.Pool.Command) : IO Json := do
  IO.ofExcept (← exchange config (fun replyTo => .event (.request replyTo command)))

/-- Poll ownership independently of user computation. A revoked or disconnected
attempt signals its local tasks, then fails outside Cloud.exec's error capture.
No replacement is acknowledged until the action and monitor have both stopped. -/
def withCancellation (config : Config) (run worker : String) (attempt : Nat)
    (revoked : IO.Ref Bool) (action : CancellationToken IO → IO Unit → IO α) : IO α :=
  withHeartbeat config run worker attempt fun healthy => do
    let stopped ← IO.mkRef false
    let cancelled ← IO.mkRef false
    let failure ← IO.mkRef (none : Option IO.Error)
    let check : IO Unit := do
      if let some error ← failure.get then throw error
      if ← revoked.get then throw (IO.userError "Assignment revoked")
      healthy
      let allowed : Bool ← IO.ofExcept (fromJson? (← request config (.check run worker attempt)))
      unless allowed do
        revoked.set true
        cancelled.set true
        throw (IO.userError "Assignment revoked")
    check
    let monitor ← IO.asTask (do
      let mut next := (← IO.monoMsNow) + 1000
      while !(← stopped.get) do
        if (← IO.monoMsNow) ≥ next then
          try check
          catch error =>
            cancelled.set true
            failure.set (some error)
            return
          next := (← IO.monoMsNow) + 1000
        IO.sleep 50) .dedicated
    try action ⟨cancelled.get⟩ check
    finally
      stopped.set true
      discard (IO.wait monitor)

def control (config : Config) (requestId : String) (command : LeanCloud.Pool.Command) : IO (Except String Unit) := do
  validateRun requestId
  return (← exchange config (fun replyTo => .control replyTo requestId command)).map (fun _ => ())

def configure (config : Config) (routes : Array HttpMailbox.WorkerEndpoint) : IO Json := do
  IO.ofExcept ({ config.mailboxes with workers := routes }.validate)
  IO.ofExcept (← exchange config (fun replyTo => .configure replyTo routes))

private def reconfigure (config : Config) (saved : Saved)
    (routes : Array HttpMailbox.WorkerEndpoint) : Except String Saved := do
  ({ config.mailboxes with workers := routes } : HttpMailbox.Mailboxes).validate
  let (state, _) ← LeanCloud.Pool.command saved.state (.configureWorkers (routes.map (·.worker)))
  let retained := saved.routes.getD config.mailboxes.workers
  let retained := routes.foldl (fun all route =>
    (all.filter (·.worker != route.worker)).push route) retained
  return { saved with state, routes := some retained }

/-- An offline worker must not block pool administration. Readiness retries
recover the current assignment or cancellation; process restart reconstructs
from the root. Report acknowledgements carry no state needed by the worker. -/
private def reply (endpoint : HttpMailbox.Config) (worker : String) (message : LeanCloud.Pool.Reply) : IO Unit := do
  try HttpMailbox.send endpoint address ("worker." ++ worker) message
  catch _ => IO.eprintln s!"Mailbox for {worker} unavailable; waiting for worker readiness."

/-- Sole owner of the deployment's SQLite database. The catalog is durable before
replies and input acknowledgements; scheduling continuations are volatile.
Administrative replies are cached until the caller's address retires. -/
def scheduler (config : Config) (record : Trace.Recorder := fun _ => pure ())
    (retire : String → IO Unit := fun _ => pure ()) : IO Unit := do
  let lock ← ProcessLock.acquire (config.scheduler.database ++ ".lock")
  try
    let conn ← LeanLinq.Sqlite.connect config.scheduler.database
    try
      LocalDb.initializeSchema conn
      let mut saved : Saved ← LocalDb.loadValue conn "pool-v1" {}
      for run in saved.state.removed do retire run
      let observed ← IO.mkRef saved.state.runs
      let emitted ← IO.mkRef (#[] : Array LeanCloud.Pool.Run)
      let persist (value : Saved) : IO Saved := do
        let before ← observed.get
        let now ← wallTime
        let timings := value.state.runs.map fun run =>
          let timing := (value.timings.find? (·.1 == run.id)).map (·.2) |>.getD {}
          (run.id, Timing.observe timing (before.find? (·.id == run.id)) run now)
        let value := { value with timings }
        LocalDb.saveValue conn "pool-v1" value
        -- Emit observations only after the associated catalog commit succeeds.
        let before ← emitted.get
        for run in value.state.runs do
          let previous := (before.find? (·.id == run.id)).map (·.scheduler.jobs) |>.getD #[]
          if previous != run.scheduler.jobs then
            (← Trace.create "scheduler" run.id record).branches previous run.scheduler.jobs
        observed.set value.state.runs
        emitted.set value.state.runs
        return value
      if saved.routes.isNone then
        saved ← IO.ofExcept (reconfigure config saved config.mailboxes.workers)
      let workers := (saved.routes.getD config.mailboxes.workers).map (·.worker)
        |>.filter (!saved.state.membership.drained.contains ·)
      saved := { saved with state := LeanCloud.Pool.recover saved.state workers }
      saved ← persist saved
      let handle ← HttpMailbox.openMailbox config.mailboxes.scheduler address "scheduler"
      try
        let inbox : Mailbox IO Envelope := HttpMailbox.inbox handle
        let mut lastTime ← IO.monoMsNow
        let mut nextCleanup := 0
        IO.println "deployment scheduler ready"
        (← IO.getStdout).flush
        repeat
          let now ← IO.monoMsNow
          saved := { saved with state := LeanCloud.Pool.tick (now - lastTime) saved.state }
          lastTime := now
          -- Replies are needed only while their non-reusable destination lives.
          -- Check while idle too, so the final request does not leak its cache.
          if now ≥ nextCleanup then
            let live ← HttpMailbox.liveReplies config.mailboxes.scheduler
            let replies := saved.replies.filter (fun r => live.contains r.1)
            if replies.size != saved.replies.size then
              saved ← persist { saved with replies }
            nextCleanup := now + 1000
          let some delivery ← inbox.receive | continue
          let replyTo := match delivery.message with
            | .configure replyTo _ | .control replyTo .. | .event (.request replyTo _) => some replyTo
            | _ => none
          if let some replyTo := replyTo then
            -- Reject delayed duplicates even after their cached reply is gone.
            -- An exchange abandoned before execution need not execute at all.
            unless (← HttpMailbox.liveReplies config.mailboxes.scheduler).contains replyTo do
              inbox.acknowledge delivery.receipt
              continue
          match delivery.message with
          | .control replyTo requestId command =>
            let (state, receipts, response) := ControlReceipts.apply saved.state saved.receipts requestId command
            -- The intent and its receipt commit in one SQLite transaction. The
            -- receipt outlives this exchange's temporary response inbox.
            saved ← persist { saved with state, receipts }
            discard <| HttpMailbox.reply config.mailboxes.scheduler replyTo response
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
              saved ← persist saved
            discard <| HttpMailbox.reply config.mailboxes.scheduler replyTo response
          | .event message =>
            let mailboxes := { config.mailboxes with workers := saved.routes.getD config.mailboxes.workers }
            match message with
            | .submit run =>
              unless saved.state.removed.contains run do
                let (state, _) ← IO.ofExcept (LeanCloud.Pool.command saved.state (.submit run))
                saved ← persist { saved with state }
            | .ready worker =>
              unless saved.state.membership.drained.contains worker do
              if let .ok endpoint := mailboxes.worker worker then
                let (state, reply) := LeanCloud.Pool.acquire config.scheduler.assignmentMs saved.state worker
                saved := { saved with state }
                saved ← persist saved
                LeanCloudRuntime.Pool.reply endpoint worker reply
                if let .execute run assignment := reply then
                  let trace ← Trace.create "scheduler" run record
                  trace.assign assignment
                  trace.emit "dispatch" worker
            | .drained worker generation =>
              saved := { saved with state := LeanCloud.Pool.drained saved.state worker generation }
              saved ← persist saved
            | .stopped run worker barrier =>
              saved := { saved with state := LeanCloud.Pool.stopped saved.state run worker barrier }
              saved ← persist saved
            | .renew run worker attempt =>
              let state := LeanCloud.Pool.renew config.scheduler.assignmentMs saved.state run worker attempt
              saved := { saved with state }
              saved ← persist saved
            | .report run report =>
              unless saved.state.membership.drained.contains report.worker do
              if let .ok endpoint := mailboxes.worker report.worker then
                saved := { saved with state := LeanCloud.Pool.report saved.state run report }
                saved ← persist saved
                if let some state := saved.state.runs.find? (·.id == run) then
                  if let some error := state.scheduler.error then
                    (← Trace.create "scheduler" run record).emit "failed" error.message
                reply endpoint report.worker .acknowledged
                (← Trace.create "scheduler" run record).emit "report" report.worker
            | .request replyTo command =>
              let cached := saved.replies.find? (·.1 == replyTo)
              let (state, response) := match cached with
                | some (_, response) => (saved.state, response)
                | none => match LeanCloud.Pool.command saved.state command with
                  | .ok (state, response) => (state, .ok response)
                  | .error error => (saved.state, .error error)
              saved := { saved with state }
              let cache := match command with
                | .check .. | .status .. | .health | .workers | .runs .. | .mode .. | .removed .. | .removedRuns => false
                | _ => true
              if cache && cached.isNone then
                saved := { saved with replies := saved.replies.push (replyTo, response) }
              if cache then saved ← persist saved
              let response ← match command, response with
                | .workers, .ok json =>
                  let routes := mailboxes.workers.filter fun route =>
                    saved.state.membership.active.all (·.contains route.worker)
                  pure (.ok (json.setObjVal! "routes" (toJson routes)))
                | .status run, .ok json => do
                  let now ← wallTime
                  let timing := (saved.timings.find? (·.1 == run)).map fun (_, timing) =>
                    { timing with observedMs := max now timing.observedMs }
                  pure (.ok (json.setObjVal! "timing" (toJson timing)))
                | _, response => pure response
              if response.isOk then
                match command with
                | .pause run => (← Trace.create "scheduler" run record).emit "paused" ""
                | .resume run => (← Trace.create "scheduler" run record).emit "resumed" ""
                | .kill run => (← Trace.create "scheduler" run record).emit "killed" ""
                | _ => pure ()
              discard <| HttpMailbox.reply config.mailboxes.scheduler replyTo response
          inbox.acknowledge delivery.receipt
      finally handle.close
    finally conn.close
  finally ProcessLock.release lock

/-- Registration follows immutable definition persistence. A retried submission
cannot replace the program/input or reactivate a paused/killed process. -/
def submit (config : Config) (run : String) : IO Unit := do
  send config (.submit run)

def status (config : Config) (run : String) : IO Scheduler.Snapshot := do
  IO.ofExcept (fromJson? (← request config (.status run)))

def observation (config : Config) (run : String) : IO Timing.Status := do
  IO.ofExcept (fromJson? (← request config (.status run)))

end LeanCloudRuntime.Pool
