import LeanCloudRuntime.LocalDb
import LeanCloudRuntime.Trace
import LeanCloudRuntime.ProcessLock
import LeanCloud.DeploymentApi
import Std.Sync.Mutex

/-! Best-effort last views. Workers enqueue small observations in memory;
SQLite writes run in a separate task and never decide workflow progress. -/
namespace LeanCloudRuntime.ObservationStore
open Lean LeanCloud LeanLinq

private abbrev Row : Schema := [("run", .string), ("key", .string), ("value", .string)]
private abbrev Context : Ctx := { tables := [("observations", Row)] }
private def table : Table "observations" Row := ⟨⟩

private structure Pending where
  values : Std.HashMap (String × String) Observations.Step := {}
  warning : String := ""

structure Store where
  conn : Sqlite.Conn
  lock : Std.Mutex Unit
  pending : Std.Mutex Pending
  samples : IO.Ref (Array ResourceSample)
  worker : String

def create (conn : Sqlite.Conn) (worker : String) : IO Store := do
  conn.execRaw "PRAGMA journal_mode=WAL; PRAGMA synchronous=FULL; PRAGMA busy_timeout=5000;"
  LocalDb.ensureVersion conn "observations"
  conn.createTable table (primaryKey := [.column "run", .column "key"])
  return ⟨conn, ← Std.Mutex.new (), ← Std.Mutex.new {}, ← IO.mkRef #[], worker⟩

/-- The buffer coalesces updates and is bounded under disk pressure. A gap is
reported instead of blocking a worker on diagnostic storage. -/
def Store.record (store : Store) (step : Observations.Step) : IO Unit := do
  if step.event.run.isEmpty then return
  store.pending.atomically do
    let mut keys := step.keys
    if let some sample := step.resources then
      -- At most thirty quarter-second samples per run, including after restart.
      keys := keys.push s!"meter/{sample.timeNs / 250000000 % 30}"
    for key in keys do
      let state ← get
      let address := (step.event.run, key)
      if key.utf8ByteSize > 4096 || (state.values.size ≥ 8192 && !state.values.contains address) then
        set { state with warning := "Some observations were dropped under telemetry pressure." }
      else set { state with values := state.values.insert address step }

private def save (conn : Sqlite.Conn) (run key : String) (step : Observations.Step) : IO Unit := do
  let value := (toJson step).compress
  let update : UpdateStmt Context _ _ := table.update
    |>.set "value" (SqlExpr.str value)
    |>.where' (fun row => (row["run"] ==. SqlExpr.str run) &&. (row["key"] ==. SqlExpr.str key))
  if (← conn.execUpdate update) == 0 then
    let insert : InsertStmt Context _ _ := table.insert
      |>.value "run" (SqlExpr.str run) |>.value "key" (SqlExpr.str key) |>.value "value" (SqlExpr.str value)
    discard (conn.execInsert insert)

private def flushLocked (store : Store) : IO Unit := do
  let values ← store.pending.atomically do
    let state ← get
    set { state with values := {} }
    return state.values
  unless values.isEmpty do
    try store.conn.withTransaction do
      for ((run, key), step) in values.toArray do save store.conn run key step
    catch _ => store.pending.atomically do
      modify fun state => { state with warning := "Telemetry storage failed; the last view may have gaps." }

def Store.flush (store : Store) : IO Unit := store.lock.atomically do flushLocked store

/-- Pages have stable slot keys, not historical event offsets. Concurrent
updates are allowed; every response is an observation, not a global snapshot. -/
def Store.page (store : Store) (run : String) (after : Option String) (limit : Nat) : IO DeploymentApi.ObservationPage := do
  IO.ofExcept ((DeploymentApi.Request.observations run store.worker after limit).validate)
  store.lock.atomically do
    flushLocked store
    let query : Query Context Row := Query.from' (ts := Context) table
      |>.where' (fun row => (row["run"] ==. SqlExpr.str run) &&. (row["key"] >. SqlExpr.str (after.getD "")))
      |>.orderBy (fun row => [row["key"].asc]) |>.limit limit
    let rows ← store.conn.query query
    let mut items := #[]
    let mut cursor := none
    for .cons _ (.cons key (.cons value .nil)) in rows do
      items := items.push (← IO.ofExcept (Json.parse value >>= fromJson?))
      cursor := some key
    let warning ← store.pending.atomically do return (← get).warning
    return { items, next := if items.size == limit then cursor else none, warning }

def Store.node (store : Store) : IO DeploymentApi.Node := do
  let warning ← store.pending.atomically do return (← get).warning
  return { id := store.worker, online := true, samples := ← store.samples.get, warning }

def Store.remove (store : Store) (run : String) : IO Unit := store.lock.atomically do
  store.pending.atomically do
    modify fun state => { state with values := state.values.filter fun address _ => address.1 != run }
  let delete : DeleteStmt Context _ _ := table.delete
    |>.where' (fun row => row["run"] ==. SqlExpr.str run)
  discard (store.conn.execDelete delete)

def withStore (database : String) (worker : String) (action : Store → IO α) : IO α := do
  if let some parent := (System.FilePath.mk database).parent then IO.FS.createDirAll parent
  let lock ← ProcessLock.acquire (database ++ ".lock")
  try
    let conn ← Sqlite.connect database
    try
      let store ← create conn worker
      let stopped ← IO.mkRef false
      let task ← IO.asTask (do
        let mut next := 0
        while !(← stopped.get) do
          if (← IO.monoMsNow) ≥ next then
            if let some sample ← Trace.resources then
              store.samples.modify fun points =>
                let points := points.push sample
                points.extract (points.size - 30) points.size
            store.flush
            next := (← IO.monoMsNow) + 250
          IO.sleep 50) .dedicated
      try action store
      finally
        stopped.set true
        discard <| IO.ofExcept task.get
        store.flush
    finally conn.close
  finally ProcessLock.release lock

end LeanCloudRuntime.ObservationStore
