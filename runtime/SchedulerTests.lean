import LeanCloudRuntime.Pool
import LeanCloudRuntime.Squares
import LeanCloud.DirectInterpreter
import LeanCloudTests.Support

/-! Run the real scheduler and its durable HTTP inbox across a process crash.
The two controlled workers use the actual replay interpreter over an in-memory
journal; holding their stop replies exposes the restart barrier directly. -/
namespace SchedulerTests
open Lean LeanCloud LeanCloudRuntime LeanCloudTests

private def start (path : System.FilePath) : IO (IO.Process.Child { stdout := .piped }) := do
  let child ← IO.Process.spawn {
    cmd := (← IO.appPath).toString, args := #["pool-scheduler", path.toString], stdout := .piped }
  try
    repeat
      let line ← child.stdout.getLine
      if line.trimAscii.toString == "deployment scheduler ready" then return child
      if line.isEmpty then throw (IO.userError "Scheduler exited before readiness")
  catch error =>
    try child.kill catch _ => pure ()
    discard child.wait
    throw error

private def receive (handle : HttpMailbox.Handle) : IO LeanCloud.Pool.Reply := do
  let inbox : Mailbox IO LeanCloud.Pool.Reply := HttpMailbox.inbox handle
  let deadline := (← IO.monoMsNow) + 5000
  repeat
    unless (← IO.monoMsNow) < deadline do throw (IO.userError "Missing worker reply")
    let some item ← inbox.receive | continue
    inbox.acknowledge item.receipt
    if let .acknowledged := item.message then continue
    return item.message

private def assigned : LeanCloud.Pool.Reply → IO Assignment
  | .execute "restart-test" assignment => pure assignment
  | other => throw (IO.userError s!"Expected work, got {reprStr other}")

private def cancelled : LeanCloud.Pool.Reply → IO Nat
  | .cancel "restart-test" barrier => pure barrier
  | other => throw (IO.userError s!"Expected cancellation, got {reprStr other}")

private def idle (reply : LeanCloud.Pool.Reply) : IO Unit :=
  match reply with
  | .idle => pure ()
  | other => throw (IO.userError s!"Replacement started before all workers stopped: {reprStr other}")

def run : IO Unit := IO.FS.withTempFile fun _ inboxPath =>
    IO.FS.withTempFile fun _ database => IO.FS.withTempFile fun _ configPath => do
  let conn ← LeanLinq.Sqlite.connect inboxPath.toString
  let observer ← LeanLinq.Sqlite.connect database.toString
  try
    let handler : HttpMailbox.ServerHandler := ⟨← Inbox.create conn 400, "restart", fun _ => pure Json.null⟩
    let server ← (HttpServer.start (.v4 ⟨.ofParts 127 0 0 1, 0⟩) handler).block
    try
      let some (.v4 bound) := server.localAddr | throw (IO.userError "No HTTP address")
      let endpoint : HttpMailbox.Config := ⟨"127.0.0.1", bound.port.toNat, "restart"⟩
      let defaults : Config ← IO.ofExcept (Json.parse (include_str "../deploy/config.json") >>= fromJson?)
      let config := { defaults with
        mailboxes := ⟨endpoint, #[⟨"worker1", endpoint⟩, ⟨"worker2", endpoint⟩]⟩
        scheduler := ⟨database.toString, 30000⟩ }
      IO.FS.writeFile configPath (toJson config).compress
      let first ← HttpMailbox.openMailbox endpoint LeanCloudRuntime.Pool.address "worker.worker1"
      let second ← HttpMailbox.openMailbox endpoint LeanCloudRuntime.Pool.address "worker.worker2"
      let child ← IO.mkRef (some (← start configPath))
      let stop : IO Unit := do
        let current ← child.get
        child.set none
        if let some current := current then
          let killed ← IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString current.pid] }
          assertEq killed.exitCode 0
          discard current.wait
      try
        let records ← IO.mkRef ([] : List (String × ReplayRecord))
        let reads ← IO.mkRef (0 : Nat)
        let store : ReplayStore IO := {
          read := fun key => do reads.modify (· + 1); return (← records.get).lookup key
          create := fun key proposed => records.modifyGet fun all =>
            match all.lookup key with
            | some existing => (existing, all)
            | none => (proposed, (key, proposed) :: all) }
        let blobs : BlobStorage IO := {
          putBlob := fun _ => throw ⟨.unsupported, "No user blobs in this test"⟩
          readBlob := fun _ => throw ⟨.unsupported, "No user blobs in this test"⟩
          resolveBlob := fun _ => throw ⟨.unsupported, "No user blobs in this test"⟩ }
        let execute (worker : String) (job : Assignment) :=
          Worker.execute worker ⟨store, pure #[]⟩ blobs 1000 Squares.workflow #[2, 3] job
        let ready (worker : String) (handle : HttpMailbox.Handle) := do
          LeanCloudRuntime.Pool.send config (.ready worker)
          receive handle
        let report (value : Report) := do
          LeanCloudRuntime.Pool.send config (.report "restart-test" value)
          discard <| LeanCloudRuntime.Pool.request config .health
        discard <| LeanCloudRuntime.Pool.request config (.submit "restart-test")
        let root ← assigned (← ready "worker1" first)
        report (← execute "worker1" root)
        let left ← assigned (← ready "worker1" first)
        let right ← assigned (← ready "worker2" second)
        assertEq left.branchStart (Location.root.child 0)
        assertEq right.branchStart (Location.root.child 1)
        report (← execute "worker1" left)
        -- The second worker commits its result but has not delivered its reply.
        let late ← execute "worker2" right
        let committed ← records.get
        let readCount ← reads.get
        stop
        let saved : Json ← LocalDb.loadValue observer "pool-v1" Json.null
        let runs ← IO.ofExcept (saved.getObjVal? "state" >>= (·.getObjValAs? (Array Json) "runs"))
        let catalog ← IO.ofExcept (runs[0]!.getObjVal? "scheduler")
        for field in ["jobs", "pending", "continuation", "stopping"] do
          assertTrue (!(catalog.getObjVal? field).isOk) s!"Persisted traversal field: {field}"
        IO.sleep 500 -- retire the crashed scheduler's inbox session
        child.set (some (← start configPath))
        let barrier ← cancelled (← ready "worker1" first)
        assertEq (← cancelled (← ready "worker2" second)) barrier
        let valid : Bool ← IO.ofExcept (fromJson? (← LeanCloudRuntime.Pool.request config
          (.check "restart-test" "worker2" right.attempt)))
        assertTrue (!valid) "Restart kept an old attempt valid"
        LeanCloudRuntime.Pool.send config (.stopped "restart-test" "worker1" barrier)
        idle (← ready "worker1" first)
        report late
        LeanCloudRuntime.Pool.send config (.stopped "restart-test" "worker2" (barrier - 1))
        idle (← ready "worker1" first)
        assertEq (← records.get) committed "Scheduler changed the journal during recovery"
        assertEq (← reads.get) readCount "Scheduler read the journal during recovery"
        LeanCloudRuntime.Pool.send config (.stopped "restart-test" "worker2" barrier)
        let resumed ← assigned (← ready "worker1" first)
        assertEq resumed.branchStart Location.root "Restored a saved child instead of reconstructing from root"
        assertTrue (resumed.attempt > right.attempt) "Recovery reused an old attempt"
        let done ← execute "worker1" resumed
        assertOutcome done.progress (.ok .done)
        report done
        assertTrue (← LeanCloudRuntime.Pool.status config "restart-test").finished "Root reply did not complete scheduling"
        let expected ← (DirectInterpreter.interpret blobs Squares.workflow #[2, 3]).run
        let .ok (some outcome) ← (store.outcome Location.root).run | throw (IO.userError "Missing root result")
        let actual : Except CloudError Nat ← (ReplayInterpreter.result outcome).run
        assertOutcome actual expected
        for (key, record) in committed do
          assertEq ((← records.get).lookup key) (some record) "Replay replaced an existing record"
        IO.println "Recursive scheduling, catalog-only recovery, two-worker stop barrier, and replayed result passed"
      finally
        stop
        first.close
        second.close
    finally server.shutdownAndWait.block
  finally
    observer.close
    conn.close

end SchedulerTests
