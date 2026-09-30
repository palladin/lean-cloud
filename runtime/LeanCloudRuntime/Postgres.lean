import LeanCloud.Worker
import LeanLinq.Driver.Postgres

namespace LeanCloudRuntime.Postgres
open Lean LeanLinq

structure Config where
  connection : String
  deriving FromJson, ToJson

private abbrev RecordSchema : Schema := [("run", .string), ("key", .string), ("value", .string)]
private abbrev Context : Ctx := { tables := [("cloud_records", RecordSchema)] }
private def records : Table "cloud_records" RecordSchema := ⟨⟩

def initializeSchema (conn : Pg.Conn) : IO Unit :=
  conn.createTable records (primaryKey := [.column "run", .column "key"])

def get (conn : Pg.Conn) (run key : String) : IO (Option Json) := do
  let query : Query Context [("value", .string)] :=
    Query.from' (ts := Context) records
      |>.where' (fun row => row["run"] ==. SqlExpr.str run)
      |>.where' (fun row => row["key"] ==. SqlExpr.str key)
      |>.select (fun row => ![row["value"].as "value"])
  match ← conn.query query with
  | [] => return none
  | [.cons text .nil] =>
    match Json.parse text with
    | .ok value => return some value
    | .error _ => throw (IO.userError "Invalid JSON in cloud record")
  | _ => throw (IO.userError "Duplicate cloud record")

/-- The unique constraint arbitrates concurrent writers. A duplicate never
overwrites the winner. After an insert error, success requires observing the
same durable JSON value; otherwise preserve the original infrastructure error
or return false for a conflicting value. No SELECT-then-UPDATE race. -/
def put (conn : Pg.Conn) (run key : String) (value : Json) : IO Bool := do
  let statement : InsertStmt Context "cloud_records" RecordSchema :=
    records.insert |>.value "run" (SqlExpr.str run)
      |>.value "key" (SqlExpr.str key) |>.value "value" (SqlExpr.str value.compress)
  try
    let count ← conn.execInsert statement
    return count == 1
  catch error =>
    match ← get conn run key with
    | some existing => return existing == value
    | none => throw error

def db (conn : Pg.Conn) (run : String) : LeanCloud.Db Unit IO where
  get key state := return (← get conn run key, state)
  put key value state := return (← put conn run key value, state)

def connect (config : Config) (run : String) : IO (LeanCloud.Worker.Connection (LeanCloud.Db Unit IO)) := do
  let conn ← Pg.connect config.connection
  return ⟨db conn run, conn.close⟩

end LeanCloudRuntime.Postgres
