import LeanCloud.Worker
import LeanCloudCli.Http
import LeanCloudRuntime.Inbox
import LeanCloudRuntime.ProcessLock
import Std.Http
import LeanCloudRuntime.HttpServer

namespace LeanCloudRuntime.HttpMailbox
open Lean LeanCloud

structure Config where
  host : String
  port : Nat := 8080
  token : String := "local-cloud"
  deriving FromJson, ToJson, Inhabited

structure WorkerEndpoint where
  worker : WorkerId
  endpoint : Config
  deriving FromJson, ToJson, Inhabited

structure Mailboxes where
  scheduler : Config
  workers : Array WorkerEndpoint
  deriving FromJson, ToJson

def Mailboxes.worker (config : Mailboxes) (id : WorkerId) : Except String Config := do
  let some node := config.workers.find? (·.worker == id)
    | throw s!"No HTTP inbox configured for worker '{id}'"
  return node.endpoint

def Mailboxes.validate (config : Mailboxes) : Except String Unit := do
  let mut ids : Array String := #[]
  for node in config.workers do
    unless !node.worker.isEmpty && node.worker.length ≤ 64 && node.worker.toList.all (fun c =>
        c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_')) do
      throw "Worker ids must contain 1–64 ASCII letters, digits, '-' or '_'"
    if ids.contains node.worker then throw s!"Duplicate worker inbox: {node.worker}"
    ids := ids.push node.worker
  for endpoint in #[config.scheduler] ++ config.workers.map (·.endpoint) do
    unless !endpoint.host.isEmpty && endpoint.host.toList.all (fun c => c.isAlphanum || c == '.' || c == '-') &&
        0 < endpoint.port && endpoint.port ≤ 65535 && !endpoint.token.isEmpty &&
        !(endpoint.token.contains '\r') && !(endpoint.token.contains '\n') do
      throw "Each HTTP endpoint needs a hostname, a port between 1 and 65535, and a token"

def call (config : Config) (request : Inbox.Request) : IO Json := do
  let response ← LeanCloudCli.Http.post s!"http://{config.host}:{config.port}/mailbox"
    config.token (toJson request).compress 5000
  let result : Except String Json ← IO.ofExcept (Json.parse response >>= fromJson?)
  IO.ofExcept result

structure Handle where
  config : Config
  queue : String
  session : String
  closed : IO.Ref Bool
  failure : IO.Ref (Option String)
  delivered : IO.Ref (Option Nat)
  heartbeat : Task (Except IO.Error Unit)

def Handle.check (handle : Handle) : IO Unit := do
  if ← handle.closed.get then throw (IO.userError "Mailbox handle is closed")
  if let some error ← handle.failure.get then throw (IO.userError error)

def Handle.operation (handle : Handle) (operation : Inbox.Operation) : IO Json := do
  handle.check
  call handle.config ⟨handle.queue, handle.session, operation⟩

def Handle.close (handle : Handle) : IO Unit := do
  handle.closed.set true
  discard <| IO.ofExcept handle.heartbeat.get
  -- Release is best effort: an unavailable service recovers through expiration
  -- or restart. Never replace an original failure with a cleanup failure.
  try discard <| call handle.config ⟨handle.queue, handle.session, .close⟩ catch _ => pure ()

def Handle.delete (handle : Handle) : IO Unit := discard (handle.operation .delete)

private def acquireSession (config : Config) (queue session : String) (waitMs : Nat) : IO Nat := do
  -- When the consumer alone restarts, its previous session may still be
  -- leased by a surviving inbox service. Wait for expiry, never steal it.
  let deadline := (← IO.monoMsNow) + waitMs
  repeat
    try return ← IO.ofExcept (fromJson? (← call config ⟨queue, session, .open⟩))
    catch error =>
      unless error.toString == "Inbox already has an active consumer" && (← IO.monoMsNow) < deadline do
        throw error
      IO.sleep 100

private def openHandle (config : Config) (acquire : String → IO (String × Nat)) : IO Handle := do
  let random ← IO.Process.output { cmd := "openssl", args := #["rand", "-hex", "16"] }
  unless random.exitCode == 0 do throw (IO.userError "Cannot allocate consumer session")
  let session := random.stdout.trimAscii.toString
  let closed ← IO.mkRef false
  let failure ← IO.mkRef none
  let (queue, lease) ← acquire session
  let heartbeat ← IO.asTask (do
    let mut next := (← IO.monoMsNow) + lease / 3
    while !(← closed.get) do
      IO.sleep 100
      if !(← closed.get) && (← IO.monoMsNow) ≥ next then
        try
          discard <| call config ⟨queue, session, .renew⟩
          next := (← IO.monoMsNow) + lease / 3
        catch error =>
          failure.set (some s!"Mailbox consumer lost its session: {error}")
          return) .dedicated
  return ⟨config, queue, session, closed, failure, ← IO.mkRef none, heartbeat⟩

/-- Acquire the inbox's consumer session. Publishing alone uses `send`. -/
def openMailbox (config : Config) (run actor : String)
    (waitMs : Nat := 0) : IO Handle :=
  openHandle config fun session => do
    let queue := (toJson (run, actor)).compress
    return (queue, ← acquireSession config queue session waitMs)

/-- A reply inbox exists only for this exchange. Close, lease expiry, or service
restart retires its address permanently; late replies cannot recreate it. -/
def openReply (config : Config) : IO Handle :=
  openHandle config fun session => do
    IO.ofExcept (fromJson? (← call config ⟨"", session, .openReply⟩))

def liveReplies (config : Config) : IO (Array String) := do
  IO.ofExcept (fromJson? (← call config ⟨"", "", .liveReplies⟩))

/-- False means the caller has gone away. Transport errors still propagate so
the scheduler retries committed commands before acknowledging their input. -/
def reply [ToJson α] (config : Config) (queue : String) (message : α) : IO Bool := do
  IO.ofExcept (fromJson? (← call config ⟨queue, "", .reply (toJson message).compress⟩))

def Handle.send [ToJson α] (handle : Handle) (message : α) : IO Unit :=
  discard (handle.operation (.send (toJson message).compress))

def inbox [FromJson α] (handle : Handle) : Mailbox IO α where
  receive := do
    handle.check
    if (← handle.delivered.get).isSome then return none
    let delivery : Option Inbox.Delivery ← IO.ofExcept (fromJson? (← handle.operation .receive))
    let some delivery := delivery | IO.sleep 50; return none
    let message ← IO.ofExcept (Json.parse delivery.payload >>= fromJson?)
    handle.delivered.set (some delivery.receipt)
    return some ⟨delivery.receipt, message⟩
  acknowledge receipt := do
    discard (handle.operation (.acknowledge receipt))
    if (← handle.delivered.get) == some receipt then handle.delivered.set none

/-- Acceptance is returned only after the destination's SQLite commit. An
ambiguous transport failure may be retried; duplicate messages are permitted. -/
def send [ToJson α] (config : Config) (run actor : String) (message : α) : IO Unit :=
  discard (call config ⟨(toJson (run, actor)).compress, "", .send (toJson message).compress⟩)

structure ServerHandler where
  store : Inbox.Store
  token : String
  api : Json → IO Json

open Std.Http in
instance : Std.Http.Server.Handler ServerHandler where
  onFailure _ error := IO.eprintln s!"HTTP connection: {error}"
  onRequest handler request := do
    if (toString request.line.uri.path) == "/health" then
      return ← Response.ok |>.text "ok"
    let authorized := request.line.headers.get? (.mk "authorization")
    unless authorized.map toString == some ("Bearer " ++ handler.token) do
      return ← Response.new |>.status .unauthorized |>.text "Unauthorized"
    unless request.line.method == .post do
      return ← Response.new |>.status .methodNotAllowed |>.text "Expected POST"
    let result : Except String Json ← try
      let text : String ← request.body.readAll (maximumSize := some (8 * 1024 * 1024))
      let json ← IO.ofExcept (Json.parse text)
      match (toString request.line.uri.path) with
      | "/mailbox" =>
        let command ← IO.ofExcept (fromJson? json)
        pure (.ok (← Inbox.apply handler.store (← IO.monoMsNow) command))
      | "/app" => pure (.ok (← handler.api json))
      | _ => pure (.error "Unknown endpoint")
    catch error => pure (.error error.toString)
    Response.ok |>.json (toJson result).compress

/-- The HTTP server and actor live in this same process. Durable queue rows
survive a process crash; volatile consumer reservations do not. -/
def withServer (config : Config) (database : String) (api : Json → IO Json)
    (actor : IO α) (handleSignals := false) : IO α := do
  if let some parent := (System.FilePath.mk database).parent then IO.FS.createDirAll parent
  let lock ← ProcessLock.acquire (database ++ ".lock")
  try
    let conn ← LeanLinq.Sqlite.connect database
    try
      let handler : ServerHandler := ⟨← Inbox.create conn, config.token, api⟩
      let address : Std.Net.SocketAddress := .v4 ⟨.ofParts 0 0 0 0, config.port.toUInt16⟩
      let server ← (HttpServer.start address handler).block
      try
        if handleSignals then (HttpServer.stopOnSignal server).block
        actor
      finally server.shutdownAndWait.block
    finally conn.close
  finally ProcessLock.release lock

end LeanCloudRuntime.HttpMailbox
