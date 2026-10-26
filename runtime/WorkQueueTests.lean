import LeanCloudRuntime.WorkQueueStore
import LeanCloudRuntime.Parallel
import TestServices
import LeanCloudTests.Support

namespace WorkQueueTests
open Lean LeanCloud LeanCloudRuntime LeanCloudTests

private def request (run : String) (operation : WorkQueueStore.Operation) : WorkQueueStore.Request :=
  ⟨(toJson (run, "build")).compress, operation⟩

private def receive (conn : LeanLinq.Sqlite.Conn) (now : Nat) (run := "run") : IO (Array WorkDelivery) := do
  IO.ofExcept (fromJson? (← WorkQueueStore.apply conn now (request run (.receive 10)) 100))

private def rejects (action : IO α) : IO Unit := do
  let rejected ← try discard action; pure false catch _ => pure true
  assertTrue rejected "Invalid queue operation succeeded"

def run : IO Unit := do
  IO.FS.withTempFile fun _ path => do
    let conn ← LeanLinq.Sqlite.connect path.toString
    let receipt ← try
      WorkQueueStore.initializeSchema conn
      discard <| WorkQueueStore.apply conn 0 (request "run" (.send #[⟨"A", toJson "A"⟩, ⟨"B", toJson "B"⟩]))
      assertTrue (← receive conn 0 "other").isEmpty "Queue crossed run boundary"
      let batch ← receive conn 0
      assertEq batch.size 2
      assertTrue (← receive conn 99).isEmpty "A live lease was delivered twice"
      assertEq (← WorkQueueStore.apply conn 99 (request "run" .idle)) (toJson false)
        "Leased work was mistaken for completion"
      discard <| WorkQueueStore.apply conn 99 (request "run" (.acknowledge batch[0]!.receipt))
      pure batch[1]!.receipt
    finally conn.close
    let conn ← LeanLinq.Sqlite.connect path.toString
    try
      WorkQueueStore.initializeSchema conn
      let batch ← receive conn 100
      assertEq (batch.map (·.value)) #[toJson "B"] "Restart lost leased work"
      assertTrue (batch[0]!.receipt != receipt) "Redelivery reused the receipt"
      discard <| WorkQueueStore.apply conn 101 (request "run" (.acknowledge receipt))
      assertEq (← WorkQueueStore.apply conn 101 (request "run" .idle)) (toJson false)
        "Stale ACK deleted a newer lease"
      rejects (WorkQueueStore.apply conn 101 (request "run" (.renew receipt)))
      rejects (WorkQueueStore.apply conn 101 (request "run" (.release receipt)))
      let receipt := batch[0]!.receipt
      discard <| WorkQueueStore.apply conn 150 (request "run" (.renew receipt)) 100
      assertTrue (← receive conn 200).isEmpty "Renewal did not extend the lease"
      discard <| WorkQueueStore.apply conn 201 (request "run" (.release receipt))
      let next ← receive conn 201
      assertEq next.size 1 "Released work was lost"
      discard <| WorkQueueStore.apply conn 202 (request "run" (.acknowledge next[0]!.receipt))
      assertEq (← WorkQueueStore.apply conn 202 (request "run" .idle)) (toJson true)
      discard <| WorkQueueStore.apply conn 203 (request "run" (.send #[⟨"B", toJson "B"⟩]))
      assertEq (← WorkQueueStore.apply conn 203 (request "run" .idle)) (toJson true)
        "Republishing an acknowledged key recreated work"
      rejects (WorkQueueStore.apply conn 203 (request "run" (.send #[⟨"B", toJson "changed"⟩])))
      rejects (WorkQueueStore.apply conn 203 (request "run" (.send
        #[⟨"new", toJson "new"⟩, ⟨"B", toJson "changed"⟩])))
      assertEq (← WorkQueueStore.apply conn 203 (request "run" .idle)) (toJson true)
        "Failed publication committed part of a batch"
      discard <| WorkQueueStore.apply conn 203 (request "run" (.send #[⟨"pending", toJson "pending"⟩]))
      discard <| WorkQueueStore.apply conn 203 (request "other" (.send #[⟨"B", toJson "retained"⟩]))
      discard <| WorkQueueStore.apply conn 204 (request "run" .retire)
      rejects (WorkQueueStore.apply conn 205 (request "run" (.send #[⟨"late", Json.null⟩])))
      rejects (receive conn 205)
      assertEq (← receive conn 205 "other").size 1 "Retirement deleted another run"
    finally conn.close
  TestServices.withMailboxes 1 fun endpoints => do
    let queue := (HttpMailbox.workQueues endpoints[0]! "concurrent").open "modules"
    let items := (Array.range 100).map fun n => ⟨toString n, toJson n⟩
    discard <| Parallel.map 8 (Array.range 8) fun _ => queue.send items
    let seen ← Std.Mutex.new (#[] : Array Nat)
    discard <| Parallel.map 8 (Array.range 8) fun _ => do
      repeat
        let messages ← queue.receive 7
        if messages.isEmpty then return ()
        for message in messages do
          let value : Nat ← IO.ofExcept (fromJson? message.value)
          seen.atomically (modify (·.push value))
          queue.renew message.receipt
          queue.acknowledge message.receipt
    assertEq ((← seen.atomically get).qsort (· < ·)) (Array.range 100)
      "Competing HTTP consumers lost or duplicated work"
    assertTrue (← queue.isIdle) "Acknowledged work remained queued"
    HttpMailbox.retireWorkQueues endpoints[0]! "concurrent"
    rejects (queue.send #[⟨"late", Json.null⟩])
  IO.println "Work queues: idempotent sends, leases, restart, stale receipts, retirement, concurrent HTTP consumers passed"

end WorkQueueTests
