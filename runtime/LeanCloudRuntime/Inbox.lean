import LeanCloudRuntime.LocalDb
import Std.Sync.Mutex

namespace LeanCloudRuntime.Inbox
open Lean LeanLinq

abbrev MessageSchema : Schema := [("queue", .string), ("id", .int), ("payload", .string)]
abbrev CounterSchema : Schema := [("queue", .string), ("next", .int)]
abbrev Context : Ctx := { tables := [("inbox_messages", MessageSchema), ("inbox_counters", CounterSchema)] }
private def messages : Table "inbox_messages" MessageSchema := ⟨⟩
private def counters : Table "inbox_counters" CounterSchema := ⟨⟩

structure Delivery where
  receipt : Nat
  payload : String
  deriving ToJson, FromJson, BEq, Repr

inductive Operation where
  | send (payload : String)
  | openReply
  | reply (payload : String)
  | liveReplies
  | open
  | renew
  | receive
  | acknowledge (receipt : Nat)
  | close
  | delete
  deriving ToJson, FromJson

structure Request where
  queue : String
  session : String := ""
  operation : Operation
  deriving ToJson, FromJson

structure Consumer where
  queue : String
  session : String
  expires : Nat
  pending : Option Delivery := none
  acknowledged : Option Nat := none

structure State where
  consumers : Array Consumer := #[]
  nextReply : Nat := 0

/-- Reply addresses are allocated by the service, never reopened by a caller.
The second prefix is reserved for reply queues from older deployments. -/
private def replyPrefixes := #["$reply/", "[\"pool-v1\",\"reply-"]

private def isReply (queue : String) : Bool := replyPrefixes.any (fun p => queue.startsWith p)

private def erase (conn : Sqlite.Conn) (pattern : String) (matchPrefix := false) : IO Unit :=
  conn.withTransaction do
    let predicate {ts : Ctx} (column : SqlExpr ts .string) :=
      if matchPrefix then SqlExprP.like column.widen (SqlExpr.str (pattern ++ "%"))
      else column ==. SqlExpr.str pattern
    let deleteMessages : DeleteStmt Context _ _ := messages.delete
      |>.where' (fun r => predicate r["queue"])
    let deleteCounter : DeleteStmt Context _ _ := counters.delete
      |>.where' (fun r => predicate r["queue"])
    discard (conn.execDelete deleteMessages)
    discard (conn.execDelete deleteCounter)

/-- One process owns the connection. The mutex covers the complete transaction,
including reservation bookkeeping; HTTP handlers never interleave SQL statements.
Actor reservations are volatile: reopening makes unacked actor mail ready again.
Temporary replies are discarded when the service restarts. -/
structure Store where
  conn : Sqlite.Conn
  state : Std.Mutex State
  leaseMs : Nat := 15000
  replyEpoch : String

def create (conn : Sqlite.Conn) (leaseMs := 15000) : IO Store := do
  -- Configuration only; all schema and data operations use typed lean-linq.
  conn.execRaw "PRAGMA journal_mode=WAL; PRAGMA synchronous=FULL; PRAGMA busy_timeout=5000;"
  conn.createTable messages (primaryKey := [.column "queue", .column "id"])
  conn.createTable counters (primaryKey := [.column "queue"])
  -- A service restart abandons temporary exchanges, but preserves actor mail.
  for p in replyPrefixes do erase conn p true
  let random ← IO.Process.output { cmd := "openssl", args := #["rand", "-hex", "16"] }
  unless random.exitCode == 0 do throw (IO.userError "Cannot allocate reply epoch")
  return ⟨conn, ← Std.Mutex.new {}, leaseMs, random.stdout.trimAscii.toString⟩

private def append (conn : Sqlite.Conn) (queue payload : String) : IO Unit := conn.withTransaction do
  let query : Query Context CounterSchema := Query.from' (ts := Context) counters
    |>.where' (fun r => r["queue"] ==. SqlExpr.str queue)
  let next ← match ← conn.query query with
    | [] =>
      let insert : InsertStmt Context _ _ := counters.insert
        |>.value "queue" (SqlExpr.str queue) |>.value "next" (SqlExpr.int 1)
      discard (conn.execInsert insert)
      pure (1 : Int)
    | [.cons _ (.cons next .nil)] => pure next
    | _ => throw (IO.userError "Invalid inbox counter")
  unless 0 < next && next < 9223372036854775807 do throw (IO.userError "Inbox sequence exhausted")
  let update : UpdateStmt Context _ _ := counters.update
    |>.set "next" (SqlExpr.int (next + 1))
    |>.where' (fun r => r["queue"] ==. SqlExpr.str queue)
  discard (conn.execUpdate update)
  let insert : InsertStmt Context _ _ := messages.insert
    |>.value "queue" (SqlExpr.str queue) |>.value "id" (SqlExpr.int next)
    |>.value "payload" (SqlExpr.str payload)
  discard (conn.execInsert insert)

private def first (conn : Sqlite.Conn) (queue : String) : IO (Option Delivery) := do
  let query : Query Context MessageSchema := Query.from' (ts := Context) messages
    |>.where' (fun r => r["queue"] ==. SqlExpr.str queue)
    |>.orderBy (fun r => [r["id"].asc]) |>.limit 1
  match ← conn.query query with
  | [] => return none
  | [.cons _ (.cons id (.cons payload .nil))] => return some ⟨id.toNat, payload⟩
  | _ => throw (IO.userError "Invalid inbox row")

/-- A supplied monotonic time makes expiration and fencing directly testable.
Time is read by the server, never trusted from an HTTP caller. -/
def apply (store : Store) (now : Nat) (request : Request) : IO Json := store.state.atomically do
  let state ← get
  for consumer in state.consumers do
    if now ≥ consumer.expires && isReply consumer.queue then erase store.conn consumer.queue
  let consumers := state.consumers.filter (fun c => now < c.expires)
  set { state with consumers }
  let { queue, session, operation } := request
  match operation with
  | .openReply =>
    unless !session.isEmpty && session.length ≤ 128 do throw (IO.userError "Invalid consumer session")
    let queue := s!"$reply/{store.replyEpoch}/{state.nextReply}"
    let consumer : Consumer := { queue, session, expires := now + store.leaseMs }
    set ({ consumers := consumers.push consumer, nextReply := state.nextReply + 1 } : State)
    return toJson (queue, store.leaseMs)
  | .liveReplies => return toJson (consumers.filterMap fun c => if isReply c.queue then some c.queue else none)
  | _ => pure ()
  unless !queue.isEmpty && queue.utf8ByteSize ≤ 512 do throw (IO.userError "Invalid inbox name")
  let current := consumers.find? (·.queue == queue)
  match operation with
  | .reply payload =>
    unless isReply queue do throw (IO.userError "Expected a temporary reply inbox")
    if current.isNone then return toJson false
    append store.conn queue payload
    return toJson true
  | .send payload =>
    if isReply queue then throw (IO.userError "Use reply delivery for temporary inboxes")
    append store.conn queue payload
    return Json.null
  | .open =>
    if isReply queue then throw (IO.userError "Reply inboxes cannot be reopened")
    unless !session.isEmpty && session.length ≤ 128 do throw (IO.userError "Invalid consumer session")
    if let some consumer := current then
      unless consumer.session == session do throw (IO.userError "Inbox already has an active consumer")
    let consumer := current.getD { queue, session, expires := now + store.leaseMs }
    modify fun s => { s with consumers := (consumers.filter (·.queue != queue)).push { consumer with expires := now + store.leaseMs } }
    return toJson store.leaseMs
  | .close =>
    -- Closing an old session cannot disturb its replacement.
    if isReply queue && current.any (·.session == session) then erase store.conn queue
    modify fun s => { s with consumers := consumers.filter (fun c => c.queue != queue || c.session != session) }
    return Json.null
  | _ =>
    let some consumer := current | throw (IO.userError "Consumer session expired")
    unless consumer.session == session do throw (IO.userError "Stale consumer session")
    let mut consumer := { consumer with expires := now + store.leaseMs }
    let response ← match operation with
      | .renew => pure Json.null
      | .receive => do
        if consumer.pending.isNone then consumer := { consumer with pending := ← first store.conn queue }
        pure (toJson consumer.pending)
      | .acknowledge receipt => do
        if consumer.acknowledged == some receipt then pure Json.null
        else
          let some pending := consumer.pending | throw (IO.userError "No reserved delivery")
          unless pending.receipt == receipt do throw (IO.userError "Stale delivery receipt")
          let delete : DeleteStmt Context _ _ := messages.delete
            |>.where' (fun r => (r["queue"] ==. SqlExpr.str queue) &&. (r["id"] ==. SqlExpr.int receipt))
          store.conn.withTransaction do
            unless (← store.conn.execDelete delete) == 1 do throw (IO.userError "Missing reserved delivery")
          consumer := { consumer with pending := none, acknowledged := some receipt }
          pure Json.null
      | .delete => do
        unless consumer.pending.isNone && (← first store.conn queue).isNone do
          throw (IO.userError "Cannot delete a nonempty inbox")
        -- Removing the consumer fences this session before a fresh inbox can
        -- reuse a row number. Temporary replies can also be discarded by close.
        let delete : DeleteStmt Context _ _ := counters.delete
          |>.where' (fun r => r["queue"] ==. SqlExpr.str queue)
        store.conn.withTransaction do discard (store.conn.execDelete delete)
        pure Json.null
      | _ => throw (IO.userError "Invalid consumer operation")
    let rest := consumers.filter (·.queue != queue)
    let consumers := match operation with | .delete => rest | _ => rest.push consumer
    modify fun s => { s with consumers }
    return response

end LeanCloudRuntime.Inbox
