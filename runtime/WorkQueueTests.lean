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

private def peek (conn : LeanLinq.Sqlite.Conn) (now : Nat)
    (after : Option WorkPosition := none) (count := 100) : IO (Array WorkPreview) := do
  IO.ofExcept (fromJson? (← WorkQueueStore.apply conn now (request "run" (.peek after count)) 100))

private def priorityTests : IO Unit := do
  let legacy : WorkItem ← IO.ofExcept (fromJson? (Json.mkObj [("key", toJson "A"), ("value", Json.null)]))
  assertEq legacy.priority 0 "Unprioritized send changed meaning"
  assertTrue ((fromJson? (α := WorkItem) (Json.mkObj [("key", toJson "A"),
    ("value", Json.null), ("priority", toJson "bad")])).toOption.isNone) "Invalid priority accepted"
  IO.FS.withTempFile fun _ path => do
    let conn ← LeanLinq.Sqlite.connect path.toString
    try
      WorkQueueStore.initializeSchema conn
      let send := fun values => discard <| WorkQueueStore.apply conn 0 (request "run" (.send values))
      send #[⟨"low", toJson "low", 1⟩, ⟨"first", toJson "first", 4⟩, ⟨"second", toJson "second", 4⟩]
      let first ← peek conn 0 none 1
      assertEq (first.map (·.value)) #[toJson "first"] "Peek ignored priority"
      let some entry := first[0]? | throw (IO.userError "Missing first preview")
      let position := entry.position
      let claimed : Array WorkDelivery ← IO.ofExcept (fromJson?
        (← WorkQueueStore.apply conn 0 (request "run" (.receive 1)) 100))
      assertEq (claimed.map (·.value)) (first.map (·.value)) "Peek acquired a lease or disagreed with receive"
      discard <| WorkQueueStore.apply conn 1 (request "run" (.complete claimed[0]!.receipt false))
      send #[⟨"urgent", toJson "urgent", 9⟩]
      let rest ← peek conn 2 (some position)
      assertEq (rest.map (·.value)) #[toJson "second", toJson "low"]
        "Cursor skipped a FIFO tie after the preceding item was removed"
      assertEq ((← peek conn 2).map (·.value)) #[toJson "urgent", toJson "second", toJson "low"]
        "Restarting the scan missed new higher-priority work"
      rejects (send #[⟨"first", toJson "first", 5⟩])
      rejects (send #[⟨"oversized", Json.null, 9223372036854775808⟩])
      rejects (peek conn 2 none 0)
      rejects (peek conn 2 none 101)
      assertEq (← WorkQueueStore.apply conn 2 (request "run" .progress)) (toJson (⟨1, 0⟩ : WorkQueueProgress))
        "Peeking changed durable progress"
      let claimed ← receive conn 2
      assertEq (claimed.map (·.value)) #[toJson "urgent", toJson "second", toJson "low"]
      assertTrue (← peek conn 3).isEmpty "Peek included live leases"
      discard <| WorkQueueStore.apply conn 3 (request "run" (.release claimed[1]!.receipt))
      assertEq ((← peek conn 3).map (·.value)) #[toJson "second"] "Released work lost its priority"
    finally conn.close
    let conn ← LeanLinq.Sqlite.connect path.toString
    try
      WorkQueueStore.initializeSchema conn
      assertEq ((← peek conn 102).map (·.value)) #[toJson "urgent", toJson "second", toJson "low"]
        "Restart/lease expiry lost priority or FIFO ordering"
    finally conn.close
  -- A real pre-priority database: migrate pending receipts and retained keys.
  IO.FS.withTempFile fun _ path => do
    let conn ← LeanLinq.Sqlite.connect path.toString
    try
      conn.execRaw "CREATE TABLE work_messages (queue TEXT NOT NULL, id INTEGER NOT NULL, payload TEXT NOT NULL, receipt TEXT NOT NULL, available INTEGER NOT NULL, PRIMARY KEY(queue,id)); CREATE TABLE work_submissions (queue TEXT NOT NULL, key TEXT NOT NULL, payload TEXT NOT NULL, PRIMARY KEY(queue,key)); CREATE TABLE work_counters (queue TEXT NOT NULL PRIMARY KEY, next INTEGER NOT NULL); INSERT INTO work_messages VALUES ('[\"run\",\"build\"]',1,'\"legacy\"','old-receipt',100); INSERT INTO work_submissions VALUES ('[\"run\",\"build\"]','legacy','\"legacy\"'); INSERT INTO work_counters VALUES ('[\"run\",\"build\"]',3);"
      -- Force failure after the first table rename. The transaction must leave
      -- the original data/schema intact so the same upgrade can be retried.
      conn.execRaw "CREATE TABLE work_submissions_legacy (block INTEGER);"
      rejects (WorkQueueStore.initializeSchema conn)
      conn.execRaw "DROP TABLE work_submissions_legacy;"
      WorkQueueStore.initializeSchema conn
      WorkQueueStore.initializeSchema conn
      assertTrue (← peek conn 99).isEmpty "Migration dropped a live lease"
      let rows ← peek conn 100
      assertEq (rows.map fun row => (row.value.compress, row.position.priority)) #[("\"legacy\"", 0)]
        "Migration changed legacy payload/priority"
      discard <| WorkQueueStore.apply conn 100 (request "run" (.send #[⟨"legacy", toJson "legacy", 0⟩]))
      assertEq (← peek conn 100).size 1 "Migration lost deduplication"
      let claimed ← receive conn 100
      assertTrue (claimed[0]!.receipt != "old-receipt") "Migration reused an expired receipt"
    finally conn.close

def run : IO Unit := do
  priorityTests
  -- Adopt queues written before durable progress counters were introduced.
  IO.FS.withTempFile fun _ path => do
    let conn ← LeanLinq.Sqlite.connect path.toString
    try
      WorkQueueStore.initializeSchema conn
      discard <| WorkQueueStore.apply conn 0 (request "legacy" (.send #[⟨"A", Json.null, 0⟩]))
      let batch ← receive conn 0 "legacy"
      discard <| WorkQueueStore.apply conn 1 (request "legacy" (.acknowledge batch[0]!.receipt))
      conn.execRaw "DROP TABLE work_totals"
      WorkQueueStore.initializeSchema conn
      let stats : WorkQueueProgress ← IO.ofExcept (fromJson? (← WorkQueueStore.apply conn 2 (request "legacy" .progress)))
      assertEq stats ⟨1, 0⟩ "Legacy acknowledgements were forgotten"
      discard <| WorkQueueStore.apply conn 3 (request "legacy" (.send #[⟨"B", Json.null, 0⟩]))
      let batch ← receive conn 3 "legacy"
      discard <| WorkQueueStore.apply conn 4 (request "legacy" (.complete batch[0]!.receipt true))
      let stats : WorkQueueProgress ← IO.ofExcept (fromJson? (← WorkQueueStore.apply conn 5 (request "legacy" .progress)))
      assertEq stats ⟨2, 1⟩ "First new completion double-counted legacy progress"
    finally conn.close
  IO.FS.withTempFile fun _ path => do
    let conn ← LeanLinq.Sqlite.connect path.toString
    let receipt ← try
      WorkQueueStore.initializeSchema conn
      discard <| WorkQueueStore.apply conn 0 (request "run" (.send #[⟨"A", toJson "A", 0⟩, ⟨"B", toJson "B", 0⟩]))
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
      let progress : WorkQueueProgress ← IO.ofExcept (fromJson? (← WorkQueueStore.apply conn 100 (request "run" .progress)))
      assertEq progress ⟨1, 0⟩ "Restart lost durable progress"
      let batch ← receive conn 100
      assertEq (batch.map (·.value)) #[toJson "B"] "Restart lost leased work"
      assertTrue (batch[0]!.receipt != receipt) "Redelivery reused the receipt"
      discard <| WorkQueueStore.apply conn 101 (request "run" (.acknowledge receipt))
      assertEq (← WorkQueueStore.apply conn 101 (request "run" .idle)) (toJson false)
        "Stale ACK deleted a newer lease"
      rejects (WorkQueueStore.apply conn 101 (request "run" (.renew receipt)))
      discard <| WorkQueueStore.apply conn 101 (request "run" (.release receipt))
      assertTrue (← receive conn 101).isEmpty "Stale release disturbed a newer lease"
      let receipt := batch[0]!.receipt
      discard <| WorkQueueStore.apply conn 150 (request "run" (.renew receipt)) 100
      assertTrue (← receive conn 200).isEmpty "Renewal did not extend the lease"
      discard <| WorkQueueStore.apply conn 201 (request "run" (.release receipt))
      discard <| WorkQueueStore.apply conn 201 (request "run" (.release receipt))
      let next ← receive conn 201
      assertEq next.size 1 "Released work was lost"
      discard <| WorkQueueStore.apply conn 202 (request "run" (.complete next[0]!.receipt true))
      discard <| WorkQueueStore.apply conn 202 (request "run" (.complete next[0]!.receipt true))
      discard <| WorkQueueStore.apply conn 202 (request "run" (.complete receipt true))
      let progress : WorkQueueProgress ← IO.ofExcept (fromJson? (← WorkQueueStore.apply conn 202 (request "run" .progress)))
      assertEq progress ⟨2, 1⟩ "Duplicate/expired completion inflated progress"
      let page : Array WorkCompletion ← IO.ofExcept (fromJson?
        (← WorkQueueStore.apply conn 202 (request "run" (.completions 0 1))))
      assertEq (page.map fun item => (item.cursor, item.value, item.failed)) #[(1, toJson "A", false)]
      let page : Array WorkCompletion ← IO.ofExcept (fromJson?
        (← WorkQueueStore.apply conn 202 (request "run" (.completions 1 100))))
      assertEq (page.map fun item => (item.cursor, item.value, item.failed)) #[(2, toJson "B", true)]
        "Completion feed lost ordering, restart durability, or deduplication"
      assertEq (← WorkQueueStore.apply conn 202 (request "run" .idle)) (toJson true)
      discard <| WorkQueueStore.apply conn 203 (request "run" (.send #[⟨"B", toJson "B", 0⟩]))
      assertEq (← WorkQueueStore.apply conn 203 (request "run" .idle)) (toJson true)
        "Republishing an acknowledged key recreated work"
      rejects (WorkQueueStore.apply conn 203 (request "run" (.send #[⟨"B", toJson "changed", 0⟩])))
      rejects (WorkQueueStore.apply conn 203 (request "run" (.send
        #[⟨"new", toJson "new", 0⟩, ⟨"B", toJson "changed", 0⟩])))
      assertEq (← WorkQueueStore.apply conn 203 (request "run" .idle)) (toJson true)
        "Failed publication committed part of a batch"
      discard <| WorkQueueStore.apply conn 203 (request "run" (.send #[⟨"pending", toJson "pending", 0⟩]))
      discard <| WorkQueueStore.apply conn 203 (request "other" (.send #[⟨"B", toJson "retained", 0⟩]))
      discard <| WorkQueueStore.apply conn 204 (request "run" .retire)
      rejects (WorkQueueStore.apply conn 205 (request "run" (.send #[⟨"late", Json.null, 0⟩])))
      rejects (receive conn 205)
      assertEq (← receive conn 205 "other").size 1 "Retirement deleted another run"
    finally conn.close
  TestServices.withMailboxes 1 fun endpoints => do
    let queue := (HttpMailbox.workQueues endpoints[0]! "concurrent").open "modules"
    let items := (Array.range 100).map fun n => ⟨toString n, toJson n, n % 7⟩
    discard <| Parallel.map 8 (Array.range 8) fun _ => queue.send items
    let expected := (Array.range 100).qsort fun a b => a % 7 > b % 7 || (a % 7 == b % 7 && a < b)
    let previews ← Parallel.map 4 (Array.range 4) fun _ => queue.peek none 100
    for preview in previews do
      assertEq (preview.map (·.value.compress)) (expected.map fun n => (toJson n).compress)
        "Concurrent HTTP previews changed priority order or consumed work"
    let seen ← Std.Mutex.new (#[] : Array Nat)
    discard <| Parallel.map 8 (Array.range 8) fun _ => do
      repeat
        let messages ← queue.receive 7
        if messages.isEmpty then return ()
        for message in messages do
          let value : Nat ← IO.ofExcept (fromJson? message.value)
          seen.atomically (modify (·.push value))
          queue.renew message.receipt
          queue.complete message.receipt (value % 2 == 0)
    assertEq ((← seen.atomically get).qsort (· < ·)) (Array.range 100)
      "Competing HTTP consumers lost or duplicated work"
    assertTrue (← queue.isIdle) "Acknowledged work remained queued"
    assertEq (← queue.progress) ⟨100, 50⟩ "Concurrent HTTP progress is not deduplicated"
    let page ← queue.completions 0 100
    assertEq (page.map (·.cursor)) ((Array.range 100).map (· + 1))
    assertEq ((page.map (·.value.compress)).qsort (· < ·)) ((items.map (·.value.compress)).qsort (· < ·))
    assertTrue (← queue.completions 100 100).isEmpty "Completion cursor replayed earlier entries"
    assertEq (← queue.completions 0 100 |>.map (·.map (·.cursor))) (page.map (·.cursor))
      "Reading the feed consumed another observer's entries"
    HttpMailbox.retireWorkQueues endpoints[0]! "concurrent"
    rejects (queue.send #[⟨"late", Json.null, 0⟩])
  IO.println "Work queues: priority/FIFO, non-consuming cursors, migration, leases, restart, retirement, concurrent HTTP consumers passed"

end WorkQueueTests
