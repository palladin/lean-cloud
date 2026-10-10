import LeanLinq.Driver.Sqlite
import LeanCloud.Version

namespace LeanCloudRuntime.LocalDb
open Lean LeanLinq

private abbrev Row : Schema := [("run", .string), ("state", .string)]
private abbrev Context : Ctx := { tables := [("scheduler", Row)] }
private def table : Table "scheduler" Row := ⟨⟩

private abbrev FormatSchema : Schema := [("scope", .string), ("version", .int)]
private abbrev FormatContext : Ctx := { tables := [("cloud_format", FormatSchema)] }
private def formats : Table "cloud_format" FormatSchema := ⟨⟩

/-- Check before changing domain tables or reclaiming reply rows. An absent
marker denotes the supported legacy schema; adoption only adds the marker. -/
def ensureVersion (conn : Sqlite.Conn) (scope : String) : IO Unit := conn.withTransaction do
  conn.createTable formats (primaryKey := [.column "scope"])
  let query : Query FormatContext FormatSchema := Query.from' (ts := FormatContext) formats
    |>.where' (fun r => r["scope"] ==. SqlExpr.str scope)
  match ← conn.query query with
  | [] =>
    let insert : InsertStmt FormatContext _ _ := formats.insert
      |>.value "scope" (SqlExpr.str scope)
      |>.value "version" (SqlExpr.int LeanCloud.Version.current)
    discard (conn.execInsert insert)
  | [.cons _ (.cons version .nil)] =>
    unless version ≥ 0 && version ≤ LeanCloud.Version.current do
      throw (IO.userError s!"Unsupported {scope} SQLite version {version}; use a compatible binary. Data was not migrated.")
  | _ => throw (IO.userError "Invalid SQLite format metadata")

/-- This database belongs exclusively to one scheduler process and its persistent
volume. It contains coordination metadata; replay values live in shared blobs. -/
def initializeSchema (conn : Sqlite.Conn) : IO Unit := do
  conn.execRaw "PRAGMA journal_mode=WAL; PRAGMA synchronous=FULL; PRAGMA busy_timeout=5000;"
  ensureVersion conn "scheduler"
  conn.createTable table (primaryKey := [.column "run"])

def loadValue [FromJson α] (conn : Sqlite.Conn) (run : String) (initial : α) : IO α := do
  let query : Query Context [("state", .string)] :=
    Query.from' (ts := Context) table
      |>.where' (fun row => row["run"] ==. SqlExpr.str run)
      |>.select (fun row => ![row["state"].as "state"])
  match ← conn.query query with
  | [] => return initial
  | [.cons text .nil] => IO.ofExcept (Json.parse text >>= fromJson?)
  | _ => throw (IO.userError "Duplicate scheduler state")

def saveValue [ToJson α] (conn : Sqlite.Conn) (run : String) (state : α) : IO Unit :=
  conn.withTransaction do
    let update : UpdateStmt Context "scheduler" Row := table.update
      |>.set "state" (SqlExpr.str (toJson state).compress)
      |>.where' (fun row => row["run"] ==. SqlExpr.str run)
    if (← conn.execUpdate update) == 0 then
      let insert : InsertStmt Context "scheduler" Row := table.insert
        |>.value "run" (SqlExpr.str run)
        |>.value "state" (SqlExpr.str (toJson state).compress)
      discard (conn.execInsert insert)

end LeanCloudRuntime.LocalDb
