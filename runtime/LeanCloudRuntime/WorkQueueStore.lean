import LeanCloudRuntime.LocalDb
import LeanCloud.ExecServices
import Std.Sync.Mutex
import Std.Time

namespace LeanCloudRuntime.WorkQueueStore
open Lean LeanLinq LeanCloud

private abbrev Row : Schema := [("queue", .string), ("id", .int), ("payload", .string),
  ("receipt", .string), ("available", .int)]
private abbrev Counter : Schema := [("queue", .string), ("next", .int)]
private abbrev Submission : Schema := [("queue", .string), ("key", .string), ("payload", .string)]
private abbrev Retired : Schema := [("run", .string)]
private abbrev Totals : Schema := [("queue", .string), ("completed", .int), ("failed", .int)]
private abbrev Completed : Schema := [("queue", .string), ("cursor", .int), ("payload", .string), ("failed", .bool)]
private abbrev Context : Ctx := { tables := [("work_messages", Row), ("work_counters", Counter),
  ("work_submissions", Submission), ("work_retired", Retired), ("work_totals", Totals),
  ("work_completed", Completed)] }
private def messages : Table "work_messages" Row := ⟨⟩
private def counters : Table "work_counters" Counter := ⟨⟩
private def submissions : Table "work_submissions" Submission := ⟨⟩
private def retired : Table "work_retired" Retired := ⟨⟩
private def totals : Table "work_totals" Totals := ⟨⟩
private def completed : Table "work_completed" Completed := ⟨⟩

inductive Operation where
  | send (values : Array WorkItem)
  | receive (count : Nat)
  | idle
  | acknowledge (receipt : String)
  | complete (receipt : String) (failed : Bool)
  | progress
  | completions (after count : Nat)
  | renew (receipt : String)
  | release (receipt : String)
  | retire
  deriving ToJson, FromJson

structure Request where
  queue : String
  operation : Operation
  deriving ToJson, FromJson

def initializeSchema (conn : Sqlite.Conn) : IO Unit := do
  conn.createTable messages (primaryKey := [.column "queue", .column "id"])
  conn.createTable counters (primaryKey := [.column "queue"])
  conn.createTable submissions (primaryKey := [.column "queue", .column "key"])
  conn.createTable retired (primaryKey := [.column "run"])
  conn.createTable totals (primaryKey := [.column "queue"])
  conn.createTable completed (primaryKey := [.column "queue", .column "cursor"])

private def progress (conn : Sqlite.Conn) (queue : String) : IO WorkQueueProgress := do
  let query : Query Context Totals := Query.from' (ts := Context) totals
    |>.where' (fun r => r["queue"] ==. SqlExpr.str queue)
  match ← conn.query query with
  | [] =>
    -- Older queues have no counter yet. Their retained submission keys and
    -- outstanding rows recover the completed count without reading blobs.
    let submitted : Query Context Submission := Query.from' (ts := Context) submissions
      |>.where' (fun r => r["queue"] ==. SqlExpr.str queue)
    let pending : Query Context Row := Query.from' (ts := Context) messages
      |>.where' (fun r => r["queue"] ==. SqlExpr.str queue)
    let sent := (← conn.queryCell submitted.count).getD 0
    let remaining := (← conn.queryCell pending.count).getD 0
    return ⟨(sent - remaining).toNat, 0⟩
  | [.cons _ (.cons completed (.cons failed .nil))] => return ⟨completed.toNat, failed.toNat⟩
  | _ => throw (IO.userError "Invalid queue progress")

private def settle (conn : Sqlite.Conn) (now : Nat) (queue receipt : String) (failed : Bool) : IO Unit := do
  unless !receipt.isEmpty do throw (IO.userError "Empty receipt")
  let previous ← progress conn queue
  let query : Query Context Row := Query.from' (ts := Context) messages
    |>.where' (fun r => (r["queue"] ==. SqlExpr.str queue) &&.
      (r["receipt"] ==. SqlExpr.str receipt) &&. (r["available"] >. SqlExpr.int now))
  let [.cons _ (.cons _ (.cons payload (.cons _ (.cons _ .nil))))] ← conn.query query
    | return
  let delete : DeleteStmt Context _ _ := messages.delete
    |>.where' (fun r => (r["queue"] ==. SqlExpr.str queue) &&.
      (r["receipt"] ==. SqlExpr.str receipt) &&. (r["available"] >. SqlExpr.int now))
  -- Redelivery, repeated ACKs and expired receipts cannot increment progress.
  if (← conn.execDelete delete) == 0 then return
  let insert : InsertStmt Context _ _ := completed.insert
    |>.value "queue" (SqlExpr.str queue) |>.value "cursor" (SqlExpr.int (previous.completed + 1))
    |>.value "payload" (SqlExpr.str payload) |>.value "failed" (SqlExpr.bool failed)
  discard (conn.execInsert insert)
  let update : UpdateStmt Context _ _ := totals.update
    |>.set "completed" (SqlExpr.int (previous.completed + 1))
    |>.set "failed" (SqlExpr.int (previous.failed + if failed then 1 else 0))
    |>.where' (fun r => r["queue"] ==. SqlExpr.str queue)
  if (← conn.execUpdate update) != 0 then return
  let insert : InsertStmt Context _ _ := totals.insert
    |>.value "queue" (SqlExpr.str queue)
    |>.value "completed" (SqlExpr.int (previous.completed + 1))
    |>.value "failed" (SqlExpr.int (previous.failed + if failed then 1 else 0))
  discard (conn.execInsert insert)

private def retire (conn : Sqlite.Conn) (run : String) : IO Unit := do
  let query : Query Context Retired := Query.from' (ts := Context) retired
    |>.where' (fun r => r["run"] ==. SqlExpr.str run)
  if (← conn.query query).isEmpty then
    let insert : InsertStmt Context _ _ := retired.insert |>.value "run" (SqlExpr.str run)
    discard (conn.execInsert insert)
  let all : Query Context Counter := Query.from' (ts := Context) counters
  for .cons name (.cons _ .nil) in ← conn.query all do
    let pair : String × String ← IO.ofExcept (Json.parse name >>= fromJson?)
    unless pair.1 == run do continue
    let delete : DeleteStmt Context _ _ := messages.delete
      |>.where' (fun r => r["queue"] ==. SqlExpr.str name)
    discard (conn.execDelete delete)
    let delete : DeleteStmt Context _ _ := totals.delete
      |>.where' (fun r => r["queue"] ==. SqlExpr.str name)
    discard (conn.execDelete delete)
    let delete : DeleteStmt Context _ _ := completed.delete
      |>.where' (fun r => r["queue"] ==. SqlExpr.str name)
    discard (conn.execDelete delete)
    let delete : DeleteStmt Context _ _ := submissions.delete
      |>.where' (fun r => r["queue"] ==. SqlExpr.str name)
    discard (conn.execDelete delete)
    let delete : DeleteStmt Context _ _ := counters.delete
      |>.where' (fun r => r["queue"] ==. SqlExpr.str name)
    discard (conn.execDelete delete)

private def allocate (conn : Sqlite.Conn) (queue : String) (count : Nat) : IO Nat := do
  let query : Query Context Counter := Query.from' (ts := Context) counters
    |>.where' (fun r => r["queue"] ==. SqlExpr.str queue)
  let next ← match ← conn.query query with
    | [] =>
      let insert : InsertStmt Context _ _ := counters.insert
        |>.value "queue" (SqlExpr.str queue) |>.value "next" (SqlExpr.int 1)
      discard (conn.execInsert insert)
      pure (1 : Int)
    | [.cons _ (.cons next .nil)] => pure next
    | _ => throw (IO.userError "Invalid work queue counter")
  unless 0 < next && next + count < 9223372036854775807 do
    throw (IO.userError "Work queue sequence exhausted")
  let update : UpdateStmt Context _ _ := counters.update
    |>.set "next" (SqlExpr.int (next + count))
    |>.where' (fun r => r["queue"] ==. SqlExpr.str queue)
  discard (conn.execUpdate update)
  return next.toNat

/-- The caller holds the inbox connection mutex. Wall time and leases survive
service restart. Every receive allocates new durable receipts, fencing old ACKs. -/
def apply (conn : Sqlite.Conn) (now : Nat) (request : Request)
    (leaseMs : Nat := 30000) : IO Json := conn.withTransaction do
  let { queue, operation } := request
  unless !queue.isEmpty && queue.utf8ByteSize ≤ 512 do throw (IO.userError "Invalid work queue name")
  let (run, _) : String × String ← IO.ofExcept (Json.parse queue >>= fromJson?)
  let query : Query Context Retired := Query.from' (ts := Context) retired
    |>.where' (fun r => r["run"] ==. SqlExpr.str run)
  if let .retire := operation then retire conn run; return Json.null
  unless (← conn.query query).isEmpty do throw (IO.userError "Run was removed")
  match operation with
  | .retire => return Json.null
  | .progress => return toJson (← progress conn queue)
  | .completions after count =>
    unless count > 0 && count ≤ 100 do throw (IO.userError "Completion count must be between 1 and 100")
    let query : Query Context Completed := Query.from' (ts := Context) completed
      |>.where' (fun r => (r["queue"] ==. SqlExpr.str queue) &&. (r["cursor"] >. SqlExpr.int after))
      |>.orderBy (fun r => [r["cursor"].asc]) |>.limit count
    let values ← (← conn.query query).toArray.mapM fun
      | .cons _ (.cons cursor (.cons payload (.cons failed .nil))) => do
        return (⟨cursor.toNat, ← IO.ofExcept (Json.parse payload), failed⟩ : WorkCompletion)
    return toJson values
  | .idle =>
    let query : Query Context Row := Query.from' (ts := Context) messages
      |>.where' (fun r => r["queue"] ==. SqlExpr.str queue) |>.limit 1
    return toJson (← conn.query query).isEmpty
  | .send values =>
    unless values.size ≤ 100 && values.all (fun v => !v.key.isEmpty && v.key.utf8ByteSize ≤ 512 &&
        v.value.compress.utf8ByteSize ≤ 65536) do
      throw (IO.userError "Work queue batch exceeds limits")
    if values.isEmpty then return Json.null
    let first ← allocate conn queue values.size
    for (value, i) in values.zipIdx do
      let payload := value.value.compress
      let query : Query Context Submission := Query.from' (ts := Context) submissions
        |>.where' (fun r => (r["queue"] ==. SqlExpr.str queue) &&. (r["key"] ==. SqlExpr.str value.key))
      match ← conn.query query with
      | [] => pure ()
      | [.cons _ (.cons _ (.cons previous .nil))] =>
        unless previous == payload do throw (IO.userError "Work item key has different contents")
        continue
      | _ => throw (IO.userError "Invalid work submission")
      let insert : InsertStmt Context _ _ := submissions.insert
        |>.value "queue" (SqlExpr.str queue) |>.value "key" (SqlExpr.str value.key)
        |>.value "payload" (SqlExpr.str payload)
      discard (conn.execInsert insert)
      let insert : InsertStmt Context _ _ := messages.insert
        |>.value "queue" (SqlExpr.str queue) |>.value "id" (SqlExpr.int (first + i))
        |>.value "payload" (SqlExpr.str payload)
        |>.value "receipt" (SqlExpr.str "") |>.value "available" (SqlExpr.int 0)
      discard (conn.execInsert insert)
    return Json.null
  | .receive count =>
    unless 0 < count && count ≤ 100 do throw (IO.userError "Receive count must be between 1 and 100")
    let query : Query Context Row := Query.from' (ts := Context) messages
      |>.where' (fun r => (r["queue"] ==. SqlExpr.str queue) &&. (r["available"] <=. SqlExpr.int now))
      |>.orderBy (fun r => [r["id"].asc]) |>.limit count
    let rows ← conn.query query
    if rows.isEmpty then return toJson (#[] : Array WorkDelivery)
    let first ← allocate conn queue rows.length
    let mut deliveries : Array WorkDelivery := #[]
    for (.cons _ (.cons id (.cons payload (.cons _ (.cons _ .nil)))), i) in rows.zipIdx do
      let receipt := s!"{id}:{first + i}"
      let update : UpdateStmt Context _ _ := messages.update
        |>.set "receipt" (SqlExpr.str receipt) |>.set "available" (SqlExpr.int (now + leaseMs))
        |>.where' (fun r => (r["queue"] ==. SqlExpr.str queue) &&. (r["id"] ==. SqlExpr.int id))
      discard (conn.execUpdate update)
      deliveries := deliveries.push ⟨receipt, ← IO.ofExcept (Json.parse payload)⟩
    return toJson deliveries
  | .acknowledge receipt =>
    settle conn now queue receipt false
    return Json.null
  | .complete receipt failed =>
    settle conn now queue receipt failed
    return Json.null
  | .renew receipt | .release receipt =>
    unless !receipt.isEmpty do throw (IO.userError "Empty receipt")
    let available := match operation with | .renew _ => now + leaseMs | _ => 0
    let update : UpdateStmt Context _ _ := messages.update
      |>.set "available" (SqlExpr.int available)
      |>.set "receipt" (SqlExpr.str (if available == 0 then "" else receipt))
      |>.where' (fun r => (r["queue"] ==. SqlExpr.str queue) &&.
        (r["receipt"] ==. SqlExpr.str receipt) &&. (r["available"] >. SqlExpr.int now))
    let changed ← conn.execUpdate update
    -- Release can be repeated after a lost response, including after another
    -- consumer acquires the item. Its receipt can never change that newer lease.
    if let .renew _ := operation then
      unless changed == 1 do throw (IO.userError "Work queue lease expired")
    return Json.null

/-- In-process adapter for direct execution and differential tests. Uses exactly
the same SQLite transactions as the HTTP adapter. -/
def provider (conn : Sqlite.Conn) (lock : Std.Mutex Unit) (scope : String) : QueueProvider IO :=
  ⟨fun name =>
    let call (operation : Operation) : IO Json := lock.atomically do
      let now := (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val.toNat
      apply conn now ⟨(toJson (scope, name)).compress, operation⟩
    { send values := do discard (call (.send values))
      receive count := do IO.ofExcept (fromJson? (← call (.receive count)))
      isIdle := do IO.ofExcept (fromJson? (← call .idle))
      acknowledge receipt := do discard (call (.acknowledge receipt))
      complete receipt failed := do discard (call (.complete receipt failed))
      progress := do IO.ofExcept (fromJson? (← call .progress))
      completions after count := do IO.ofExcept (fromJson? (← call (.completions after count)))
      renew receipt := do discard (call (.renew receipt))
      release receipt := do discard (call (.release receipt)) }⟩

end LeanCloudRuntime.WorkQueueStore
