import LeanCloud.Mailbox
import LeanLinq.Driver.Sqlite

namespace LeanCloudRuntime.LocalDb
open Lean LeanCloud LeanLinq

private abbrev Row : Schema := [("run", .string), ("state", .string)]
private abbrev Context : Ctx := { tables := [("scheduler", Row)] }
private def table : Table "scheduler" Row := ⟨⟩

/-- This database belongs exclusively to one scheduler process and its persistent
volume. It contains coordination metadata; replay values live in shared blobs. -/
def initializeSchema (conn : Sqlite.Conn) : IO Unit := do
  conn.execRaw "PRAGMA journal_mode=WAL; PRAGMA synchronous=FULL; PRAGMA busy_timeout=5000;"
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

def load (conn : Sqlite.Conn) (run : String) : IO Scheduler.State := loadValue conn run {}

def save (conn : Sqlite.Conn) (run : String) (state : Scheduler.State) : IO Unit := saveValue conn run state

def store (conn : Sqlite.Conn) (run : String) : SchedulerStore IO :=
  ⟨load conn run, save conn run⟩

end LeanCloudRuntime.LocalDb
