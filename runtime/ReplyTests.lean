import LeanCloudRuntime.Pool
import LeanCloudTests.Support

namespace ReplyTests
open Lean LeanCloud LeanCloudRuntime LeanCloudTests
open LeanLinq

private def rejects (action : IO α) : IO Unit := do
  let failed ← try discard action; pure false catch _ => pure true
  assertTrue failed "A retired reply inbox was reused"

private def contents (conn : LeanLinq.Sqlite.Conn) : IO (Nat × Nat) := do
  let messages : LeanLinq.Table "inbox_messages" Inbox.MessageSchema := ⟨⟩
  let counters : LeanLinq.Table "inbox_counters" Inbox.CounterSchema := ⟨⟩
  let rows ← conn.query (LeanLinq.Query.from' (ts := Inbox.Context) messages)
  let queues ← conn.query (LeanLinq.Query.from' (ts := Inbox.Context) counters)
  return (rows.length, queues.length)

/-- The supplied clock exercises abandonment without sleeping. Real SQLite rows,
including unacknowledged replies and counters, must be reclaimed. Actor mail stays. -/
private def inboxes : IO Unit := IO.FS.withTempFile fun _ path => do
  let conn ← LeanLinq.Sqlite.connect path.toString
  try
    let mut store ← Inbox.create conn 100
    discard <| Inbox.apply store 0 ⟨"actor", "", .send "durable work"⟩
    -- Upgrade from the old, indefinitely durable request/reply implementation.
    let legacy := (toJson ("pool-v1", "reply-before-upgrade")).compress
    let messages : Table "inbox_messages" Inbox.MessageSchema := ⟨⟩
    let counters : Table "inbox_counters" Inbox.CounterSchema := ⟨⟩
    let message : InsertStmt Inbox.Context _ _ := messages.insert
      |>.value "queue" (SqlExpr.str legacy) |>.value "id" (SqlExpr.int 1)
      |>.value "payload" (SqlExpr.str "abandoned")
    let counter : InsertStmt Inbox.Context _ _ := counters.insert
      |>.value "queue" (SqlExpr.str legacy) |>.value "next" (SqlExpr.int 2)
    discard (conn.execInsert message)
    discard (conn.execInsert counter)
    store ← Inbox.create conn 100
    assertEq (← contents conn) (1, 1) "Legacy reply inbox was not reclaimed"
    for i in [:240] do
      let now := i * 1000
      let (queue, lease) : String × Nat ← IO.ofExcept (fromJson? (← Inbox.apply store now ⟨"", "client", .openReply⟩))
      assertEq lease 100
      let reply (store : Inbox.Store) (time : Nat) : IO Bool := do
        IO.ofExcept (fromJson? (← Inbox.apply store time ⟨queue, "", .reply "result"⟩))
      assertTrue (← reply store now) "Live reply was refused"
      discard <| Inbox.apply store now ⟨queue, "client", .receive⟩
      discard <| Inbox.apply store now ⟨queue, "stale", .close⟩
      assertEq (← contents conn) (2, 2) "Stale close removed a live reply"
      match i % 3 with
      | 0 => discard <| Inbox.apply store now ⟨queue, "client", .close⟩
      | 1 => discard <| Inbox.apply store (now + 100) ⟨"", "", .liveReplies⟩
      | _ => store ← Inbox.create conn 100
      assertTrue (!(← reply store (now + 101))) "Late reply recreated retired rows"
      rejects (Inbox.apply store (now + 101) ⟨queue, "client", .open⟩)
      rejects (Inbox.apply store (now + 101) ⟨queue, "client", .renew⟩)
      rejects (Inbox.apply store (now + 101) ⟨queue, "", .send "late"⟩)
      assertEq (← contents conn) (1, 1) s!"Temporary rows leaked at iteration {i}"
      let live : Array String ← IO.ofExcept (fromJson? (← Inbox.apply store (now + 101) ⟨"", "", .liveReplies⟩))
      assertEq live #[]
    discard <| Inbox.apply store 300000 ⟨"actor", "worker", .open⟩
    let item : Option Inbox.Delivery ← IO.ofExcept (fromJson? (← Inbox.apply store 300000 ⟨"actor", "worker", .receive⟩))
    assertEq (item.map (·.payload)) (some "durable work")
  finally conn.close

private def response (handle : HttpMailbox.Handle) : IO (Except String Json) := do
  let inbox : Mailbox IO (Except String Json) := HttpMailbox.inbox handle
  let deadline := (← IO.monoMsNow) + 5000
  repeat
    unless (← IO.monoMsNow) < deadline do throw (IO.userError "Missing administrative reply")
    let some delivery ← inbox.receive | continue
    inbox.acknowledge delivery.receipt
    return delivery.message

private def start (path : System.FilePath) : IO (IO.Process.Child { stdout := .piped }) := do
  let child ← IO.Process.spawn {
    cmd := (← IO.appPath).toString
    args := #["pool-scheduler", path.toString], stdout := .piped }
  try
    repeat
      let line ← child.stdout.getLine
      if line.trimAscii.toString == "deployment scheduler ready" then return child
      if line.isEmpty then throw (IO.userError "Scheduler exited before readiness")
  catch error =>
    try child.kill catch _ => pure ()
    discard child.wait
    throw error

private def stop (child : IO.Process.Child cfg) : IO Unit := do
  child.kill
  discard child.wait

/-- Exercise the real scheduler across actor crashes with its inbox still alive.
Retained replies protect duplicate controls; retirement fences delayed duplicates
after the cache is gone. Many calls must not grow temporary durable state. -/
private def scheduler : IO Unit := IO.FS.withTempFile fun _ inboxPath =>
    IO.FS.withTempFile fun _ database => IO.FS.withTempFile fun _ configPath => do
  let conn ← LeanLinq.Sqlite.connect inboxPath.toString
  let observer ← LeanLinq.Sqlite.connect database.toString
  try
    let store ← Inbox.create conn 600
    let server ← (HttpServer.start (.v4 ⟨.ofParts 127 0 0 1, 0⟩)
      ({ store, token := "cleanup", api := fun _ => pure Json.null } : HttpMailbox.ServerHandler)).block
    try
      let some (.v4 bound) := server.localAddr | throw (IO.userError "Missing server address")
      let endpoint : HttpMailbox.Config := ⟨"127.0.0.1", bound.port.toNat, "cleanup"⟩
      let defaults : Config ← IO.ofExcept (Json.parse (include_str "../deploy/config.json") >>= fromJson?)
      let config := { defaults with
        mailboxes := ⟨endpoint, #[⟨"worker1", endpoint⟩]⟩
        scheduler := { defaults.scheduler with database := database.toString } }
      IO.FS.writeFile configPath (toJson config).compress
      let snapshot : IO LeanCloudRuntime.Pool.Saved := LocalDb.loadValue observer "pool-v1" {}
      let inboxContents : IO (Nat × Nat) := store.state.atomically do return ← contents conn
      let active : IO Unit := do
        discard <| LeanCloudRuntime.Pool.request config .health
        let saved ← snapshot
        assertEq ((saved.state.runs.find? (·.id == "retained")).map (·.mode)) (some .active)
      let emptyCache : IO Unit := do
        let deadline := (← IO.monoMsNow) + 5000
        repeat
          if (← snapshot).replies.isEmpty then break
          unless (← IO.monoMsNow) < deadline do throw (IO.userError "Cached replies were not reclaimed")
          IO.sleep 50
      let child ← IO.mkRef (some (← start configPath))
      let stopScheduler : IO Unit := do
        let current ← child.get
        child.set none
        if let some current := current then stop current
      try
        let rejected ← HttpMailbox.openReply endpoint
        try
          LeanCloudRuntime.Pool.send config (.request rejected.queue (.pause "retained"))
          let error ← response rejected
          assertTrue (!error.isOk) "Unknown process unexpectedly accepted"
          discard <| LeanCloudRuntime.Pool.request config (.submit "retained")
          LeanCloudRuntime.Pool.send config (.request rejected.queue (.pause "retained"))
          assertEq (toJson (← response rejected)).compress (toJson error).compress
          active
        finally rejected.close
        discard <| LeanCloudRuntime.Pool.request config (.submit "retained")
        let configured ← HttpMailbox.openReply endpoint
        let envelope := LeanCloudRuntime.Pool.Envelope.configure configured.queue config.mailboxes.workers
        let repeatConfiguration := HttpMailbox.send endpoint LeanCloudRuntime.Pool.address "scheduler" envelope
        try
          repeatConfiguration
          assertTrue (← response configured).isOk "Initial configuration failed"
          discard <| LeanCloudRuntime.Pool.configure config #[⟨"worker1", endpoint⟩, ⟨"worker2", endpoint⟩]
          repeatConfiguration
          assertTrue (← response configured).isOk "Cached configuration reply missing"
          assertEq (← snapshot).state.membership.active #["worker1", "worker2"]
        finally configured.close
        emptyCache
        repeatConfiguration
        active
        assertEq (← snapshot).state.membership.active #["worker1", "worker2"]
        for round in [:3] do
          let handle ← HttpMailbox.openReply endpoint
          let pause := LeanCloud.Pool.Message.request handle.queue (.pause "retained")
          try
            LeanCloudRuntime.Pool.send config pause
            assertTrue (← response handle).isOk "Pause failed"
            discard <| LeanCloudRuntime.Pool.request config (.resume "retained")
            LeanCloudRuntime.Pool.send config pause
            assertTrue (← response handle).isOk "Cached response missing"
            active
            stopScheduler
            IO.sleep 700 -- the actor's consumer lease expires; the client's keeps renewing
            child.set (some (← start configPath))
            LeanCloudRuntime.Pool.send config pause
            assertTrue (← response handle).isOk "Restart lost cached response"
            active
          finally handle.close
          emptyCache
          -- This delayed duplicate now has no cache to consult. Its retired
          -- address must prevent it from pausing the process again.
          LeanCloudRuntime.Pool.send config pause
          active
          for _ in [:20] do
            discard <| LeanCloudRuntime.Pool.request config (.pause "retained")
            discard <| LeanCloudRuntime.Pool.request config (.resume "retained")
          emptyCache
          assertEq (← HttpMailbox.liveReplies endpoint) #[]
          assertEq (← inboxContents) (0, 1) s!"Request state grew after round {round}"
        -- A caller vanishes before the queued command executes.
        stopScheduler
        let (abandoned, _) : String × Nat ← IO.ofExcept (fromJson? (← HttpMailbox.call endpoint ⟨"", "gone", .openReply⟩))
        LeanCloudRuntime.Pool.send config (.request abandoned (.pause "retained"))
        IO.sleep 700
        child.set (some (← start configPath))
        active
        emptyCache
        assertEq (← inboxContents) (0, 1)
        let saved ← snapshot
        assertEq saved.state.runs.size 1 "Cleanup removed workflow state"
        assertEq saved.timings.size 1 "Cleanup removed workflow timing"
      finally
        stopScheduler
    finally server.shutdownAndWait.block
  finally
    observer.close
    conn.close

def run : IO Unit := do
  inboxes
  scheduler
  IO.println "Temporary inbox reclamation, bounded reply cache, stale controls, and scheduler restarts passed"

end ReplyTests
