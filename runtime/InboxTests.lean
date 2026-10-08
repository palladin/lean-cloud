import LeanCloudRuntime.HttpMailbox
import LeanCloudRuntime.Application
import LeanCloudRuntime.Programs
import LeanCloud.MailboxModel
import LeanCloudTests.Support
import ApplicationTests
import ReplyTests

open Lean LeanCloud LeanCloudRuntime LeanCloudTests

private def rejects (action : IO α) (message : String) : IO Unit := do
  let rejected ← try discard action; pure false catch _ => pure true
  assertTrue rejected message

private def take (store : Inbox.Store) (now : Nat) (queue session : String) : IO (Option Inbox.Delivery) := do
  IO.ofExcept (fromJson? (← Inbox.apply store now ⟨queue, session, .receive⟩))

private def laws : IO Unit := IO.FS.withTempFile fun _ path => do
  let conn ← LeanLinq.Sqlite.connect path.toString
  try
    let store ← Inbox.create conn 100
    let call (now : Nat) (session : String) (op : Inbox.Operation) := Inbox.apply store now ⟨"q", session, op⟩
    discard <| call 0 "" (.send "first")
    discard <| call 0 "a" .open
    let some delivery ← take store 1 "q" "a" | throw (IO.userError "Message missing")
    assertEq delivery.payload "first"
    -- A lost receive response is recoverable, without reserving another row.
    assertEq (← take store 2 "q" "a") (some delivery)
    rejects (call 3 "b" .open) "Two active consumers acquired one inbox"
    rejects (call 3 "a" (.acknowledge (delivery.receipt + 1))) "Wrong receipt deleted a message"
    rejects (call 3 "a" .delete) "Deleted unacknowledged mail"
    discard <| call 50 "a" .renew
    rejects (call 120 "b" .open) "Renewal did not extend ownership"
    discard <| call 151 "b" .open
    rejects (call 152 "a" (.acknowledge delivery.receipt)) "Expired session acknowledged a new reservation"
    discard <| call 152 "a" .close
    let some redelivery ← take store 153 "q" "b" | throw (IO.userError "Expired delivery lost")
    assertEq redelivery.payload "first"
    discard <| call 154 "b" (.acknowledge redelivery.receipt)
    discard <| call 155 "b" (.acknowledge redelivery.receipt)
    assertEq (← take store 156 "q" "b") none
    -- Unknown commit response permits a duplicate send, but loses neither copy.
    for _ in [:2] do discard <| call 157 "" (.send "duplicate")
    for _ in [:2] do
      let some item ← take store 158 "q" "b" | throw (IO.userError "Duplicate send was lost")
      assertEq item.payload "duplicate"
      discard <| call 159 "b" (.acknowledge item.receipt)
    discard <| call 160 "b" .delete
    rejects (call 161 "b" .receive) "Deleted session remained usable"
    discard <| call 162 "" (.send "survives-reopen")
    discard <| call 163 "c" .open
    discard <| take store 164 "q" "c"
  finally conn.close
  let conn ← LeanLinq.Sqlite.connect path.toString
  try
    let store ← Inbox.create conn
    discard <| Inbox.apply store 0 ⟨"q", "d", .open⟩
    let some item ← take store 1 "q" "d" | throw (IO.userError "Reopen lost a reserved message")
    assertEq item.payload "survives-reopen"
    rejects (Inbox.apply store 2 ⟨"q", "c", .acknowledge item.receipt⟩) "Previous process session was accepted"
  finally conn.close

/-- Generated operation traces against the mailbox model used by the simulator.
Receipt numbers are opaque; compare payloads and normalize each backend's receipt. -/
private def differential (seed : Nat) : IO Unit := IO.FS.withTempFile fun _ path => do
  let conn ← LeanLinq.Sqlite.connect path.toString
  try
    let mut store ← Inbox.create conn
    let mut model : MailboxModel.Inbox String := {}
    let mut generation := 1
    let mut actualReceipt : Option Nat := none
    let mut random := seed + 1
    model := MailboxModel.connect generation model
    discard <| Inbox.apply store 0 ⟨"q", toString generation, .open⟩
    for step in [:200] do
      random := (random * 1664525 + 1013904223) % 4294967296
      let session := toString generation
      match random % 5 with
      | 0 | 1 =>
        let payload := s!"{seed}:{step}"
        model := MailboxModel.publish payload model
        discard <| Inbox.apply store 0 ⟨"q", "", .send payload⟩
      | 2 =>
        if actualReceipt.isNone then
          let (expected, next) := MailboxModel.receive generation model
          model := next
          let actual ← take store 0 "q" session
          assertEq (actual.map (·.payload)) (expected.map (·.message)) s!"seed={seed} step={step}"
          actualReceipt := actual.map (·.receipt)
      | 3 =>
        if let some actual := actualReceipt then
          let some expected := model.inFlight | throw (IO.userError "Model lost in-flight delivery")
          discard <| Inbox.apply store 0 ⟨"q", session, .acknowledge actual⟩
          model := MailboxModel.acknowledge generation expected.receipt model
          actualReceipt := none
      | _ =>
        -- Reconstruct volatile state over the same durable database.
        store ← Inbox.create conn
        model := MailboxModel.disconnect generation model
        generation := generation + 1
        model := MailboxModel.connect generation model
        actualReceipt := none
        discard <| Inbox.apply store 0 ⟨"q", toString generation, .open⟩
    if let some actual := actualReceipt then
      let some expected := model.inFlight | throw (IO.userError "Missing model reservation")
      discard <| Inbox.apply store 0 ⟨"q", toString generation, .acknowledge actual⟩
      model := MailboxModel.acknowledge generation expected.receipt model
    repeat
      let (expected, next) := MailboxModel.receive generation model
      model := next
      let actual ← take store 0 "q" (toString generation)
      assertEq (actual.map (·.payload)) (expected.map (·.message))
      match actual, expected with
      | some a, some e =>
        discard <| Inbox.apply store 0 ⟨"q", toString generation, .acknowledge a.receipt⟩
        model := MailboxModel.acknowledge generation e.receipt model
      | none, none => break
      | _, _ => throw (IO.userError "Mailbox differential mismatch")
  finally conn.close

private def http : IO Unit := IO.FS.withTempFile fun _ path => do
  let conn ← LeanLinq.Sqlite.connect path.toString
  try
    let store ← Inbox.create conn 600
    let config : Config ← IO.ofExcept (Json.parse (include_str "../deploy/config.json") >>= fromJson?)
    let handler : HttpMailbox.ServerHandler := ⟨store, "test-token", Application.api programs config (fun _ _ _ => pure ())⟩
    let server ← (HttpServer.start (.v4 ⟨.ofParts 127 0 0 1, 0⟩) handler).block
    try
      let some (.v4 bound) := server.localAddr | throw (IO.userError "No HTTP address")
      let endpoint : HttpMailbox.Config := ⟨"127.0.0.1", bound.port.toNat, "test-token"⟩
      rejects (HttpMailbox.send { endpoint with token := "wrong" } "run" "actor" (7 : Nat)) "Unauthenticated send accepted"
      HttpMailbox.send endpoint "run" "actor" (7 : Nat)
      let first ← HttpMailbox.openMailbox endpoint "run" "actor"
      try
        let inbox : Mailbox IO Nat := HttpMailbox.inbox first
        let some item ← inbox.receive | throw (IO.userError "HTTP delivery missing")
        assertEq item.message 7
        assertTrue (← inbox.receive).isNone "Adapter returned two outstanding deliveries"
        IO.sleep 1200
        rejects (HttpMailbox.openMailbox endpoint "run" "actor") "Heartbeat failed during long computation"
        inbox.acknowledge item.receipt
        assertTrue (← inbox.receive).isNone "Acknowledged message redelivered"
        first.send (9 : Nat)
        discard <| inbox.receive
      finally first.close
      let second ← HttpMailbox.openMailbox endpoint "run" "actor"
      try
        let inbox : Mailbox IO Nat := HttpMailbox.inbox second
        let some item ← inbox.receive | throw (IO.userError "Close discarded in-flight delivery")
        assertEq item.message 9
        rejects ((HttpMailbox.inbox (α := Nat) first).acknowledge item.receipt) "Closed handle acknowledged new consumer"
        inbox.acknowledge item.receipt
        second.delete
      finally second.close
      -- A separately restarted consumer waits for its old lease to expire.
      let queue := (toJson ("run", "lease")).compress
      discard <| HttpMailbox.call endpoint ⟨queue, "lost-session", .open⟩
      HttpMailbox.send endpoint "run" "lease" (11 : Nat)
      let replacement ← HttpMailbox.openMailbox endpoint "run" "lease" (waitMs := 2000)
      try
        let inbox : Mailbox IO Nat := HttpMailbox.inbox replacement
        let some item ← inbox.receive | throw (IO.userError "Restart lost leased mail")
        assertEq item.message 11
        inbox.acknowledge item.receipt
        replacement.delete
      finally replacement.close
      let response ← LeanCloudCli.Http.post s!"http://127.0.0.1:{bound.port}/app" "test-token"
        (Json.mkObj [("args", toJson #["programs"]), ("input", Json.null)]).compress
      let result : Except String Json ← IO.ofExcept (Json.parse response >>= fromJson?)
      let output : LeanCloudCli.ProcessOutput ← IO.ofExcept (result >>= fromJson?)
      assertEq output.exitCode 0
      let registered : Array ProgramInfo ← IO.ofExcept (Json.parse output.stdout >>= fromJson?)
      assertEq registered.size 2
    finally server.shutdownAndWait.block
  finally conn.close

private def signalWorker : IO Unit := do
  let server ← Std.Http.Server.new
  (HttpServer.stopOnSignal server).block
  IO.sleep 100
  IO.println "ready"
  (← IO.getStdout).flush
  repeat IO.sleep 1000

/-- The real Pool scheduler, SQLite persistence, and HTTP transport. No blob
service is needed to test work ownership while a computation is busy. -/
private def poolLeases : IO Unit := IO.FS.withTempFile fun _ inboxPath =>
    IO.FS.withTempFile fun _ schedulerPath => IO.FS.withTempFile fun _ configPath => do
  let conn ← LeanLinq.Sqlite.connect inboxPath.toString
  try
    let handler : HttpMailbox.ServerHandler := ⟨← Inbox.create conn, "lease-test", fun _ => pure Json.null⟩
    let server ← (HttpServer.start (.v4 ⟨.ofParts 127 0 0 1, 0⟩) handler).block
    try
      let some (.v4 bound) := server.localAddr | throw (IO.userError "No pool HTTP address")
      let endpoint : HttpMailbox.Config := ⟨"127.0.0.1", bound.port.toNat, "lease-test"⟩
      let defaults : Config ← IO.ofExcept (Json.parse (include_str "../deploy/config.json") >>= fromJson?)
      let config := { defaults with
        mailboxes := ⟨endpoint, #[⟨"worker1", endpoint⟩]⟩
        scheduler := ⟨schedulerPath.toString, 1500⟩ }
      IO.FS.writeFile configPath (toJson config).compress
      let child ← IO.Process.spawn {
        cmd := (← IO.appPath).toString
        args := #["pool-scheduler", configPath.toString], stdout := .piped }
      try
        assertEq (← child.stdout.getLine).trimAscii.toString "deployment scheduler ready"
        let handle ← HttpMailbox.openMailbox endpoint LeanCloudRuntime.Pool.address "worker.worker1"
        try
          let inbox : Mailbox IO LeanCloud.Pool.Reply := HttpMailbox.inbox handle
          let acquire : IO Assignment := do
            LeanCloudRuntime.Pool.send config (.ready "worker1")
            let deadline := (← IO.monoMsNow) + 5000
            repeat
              unless (← IO.monoMsNow) < deadline do throw (IO.userError "Pool did not assign work")
              let some item ← inbox.receive | continue
              inbox.acknowledge item.receipt
              if let .execute "lease-test" assignment := item.message then return assignment
          let valid (assignment : Assignment) : IO Bool := do
            IO.ofExcept (fromJson? (← LeanCloudRuntime.Pool.request config
              (.check "lease-test" "worker1" assignment.attempt)))
          discard <| LeanCloudRuntime.Pool.request config (.submit "lease-test")
          let first ← acquire
          LeanCloudRuntime.Pool.withHeartbeat config "lease-test" "worker1" first.attempt fun healthy => do
            -- No record boundaries or validity requests during the computation.
            IO.sleep 4000
            healthy
            assertTrue (← valid first) "Healthy long-running work expired"
            discard <| LeanCloudRuntime.Pool.request config (.pause "lease-test")
            IO.sleep 600
            assertTrue (!(← valid first)) "Heartbeat resurrected paused work"
          discard <| LeanCloudRuntime.Pool.request config (.resume "lease-test")
          let second ← acquire
          assertTrue (second.attempt > first.attempt) "Resume reused the old attempt"
          rejects (LeanCloudRuntime.Pool.withHeartbeat config "lease-test" "worker1" second.attempt fun _ => do
            IO.sleep 700
            throw (IO.userError "Interrupted computation") : IO Unit)
            "Computation failure was swallowed"
          IO.sleep 2000
          assertTrue (!(← valid second)) "Heartbeat outlived a failed computation"
          -- A delayed heartbeat from the previous attempt must not renew its replacement.
          let third ← acquire
          assertTrue (third.attempt > second.attempt) "Expiry reused an attempt"
          LeanCloudRuntime.Pool.withHeartbeat config "lease-test" "worker1" second.attempt fun _ => do
            IO.sleep 2000
            assertTrue (!(← valid third)) "Stale heartbeat renewed replacement work"
        finally handle.close
      finally
        try child.kill catch _ => pure ()
        discard child.wait
    finally server.shutdownAndWait.block
  finally conn.close

private def processSignals : IO Unit := do
  for signal in ["TERM", "INT"] do
    for _ in [:4] do
      let child ← IO.Process.spawn {
        cmd := (← IO.appPath).toString
        args := #["signal-worker"], stdout := .piped }
      try
        assertEq (← child.stdout.getLine).trimAscii.toString "ready" "Spurious termination signal"
        IO.sleep 100
        assertTrue (← child.tryWait).isNone "Signal waiter exited without a signal"
        let sent ← IO.Process.output { cmd := "/bin/kill", args := #["-" ++ signal, toString child.pid] }
        assertEq sent.exitCode 0
        assertEq (← child.wait) (if signal == "TERM" then 143 else 130)
      finally
        try child.kill catch _ => pure ()
        try discard child.wait catch _ => pure ()

private def crashWriter (path : String) : IO Unit := do
  let conn ← LeanLinq.Sqlite.connect path
  let store ← Inbox.create conn
  discard <| Inbox.apply store 0 ⟨"crash", "", .send "committed"⟩
  discard <| Inbox.apply store 0 ⟨"crash", "old", .open⟩
  discard <| take store 0 "crash" "old"
  IO.println "committed"
  (← IO.getStdout).flush
  repeat IO.sleep 1000

private def processCrash : IO Unit := IO.FS.withTempFile fun _ path => do
  let executable ← IO.appPath
  let child ← IO.Process.spawn {
    cmd := executable.toString
    args := #["crash-writer", path.toString]
    stdout := .piped }
  try
    assertEq (← child.stdout.getLine).trimAscii.toString "committed"
    let killed ← IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString child.pid] }
    assertEq killed.exitCode 0
    discard child.wait
    let conn ← LeanLinq.Sqlite.connect path.toString
    try
      let store ← Inbox.create conn
      discard <| Inbox.apply store 0 ⟨"crash", "new", .open⟩
      let some item ← take store 0 "crash" "new" | throw (IO.userError "SIGKILL lost committed delivery")
      assertEq item.payload "committed"
      discard <| Inbox.apply store 0 ⟨"crash", "new", .acknowledge item.receipt⟩
    finally conn.close
  finally
    try child.kill catch _ => pure ()
    try discard child.wait catch _ => pure ()

def main (args : List String) : IO UInt32 := do
  if args == ["signal-worker"] then signalWorker; return 0
  if let ["crash-writer", path] := args then crashWriter path; return 0
  if let ["pool-scheduler", path] := args then
    LeanCloudRuntime.Pool.scheduler (← Config.load path); return 0
  try
    ApplicationTests.run
    IO.println "Application commands and registry passed"
    laws
    for seed in [:32] do differential seed
    IO.println "SQLite laws and 6,400 model operations passed"
    processCrash
    IO.println "SIGKILL recovery passed"
    processSignals
    http
    poolLeases
    ReplyTests.run
    IO.println "Pool assignment renewal, pause fencing, expiry, and heartbeat cleanup passed"
    IO.println "SQLite inbox laws, 32 × 200 model operations, SIGKILL recovery, termination signals, HTTP transport, renewal, fencing, and registry API passed."
    return 0
  catch error => IO.eprintln error.toString; return 1
