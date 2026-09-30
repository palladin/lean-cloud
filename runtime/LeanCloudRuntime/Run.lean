import LeanCloudRuntime.Postgres
import LeanCloudRuntime.RabbitMQ
import LeanCloudRuntime.S3

namespace LeanCloudRuntime
open Lean LeanCloud

abbrev Config := WorkerConfig Postgres.Config RabbitMQ.Config S3.Config

structure RunDefinition where
  entry : String
  input : Json
  resultSchema : String
  deriving FromJson, ToJson

def validateRun (run : String) : IO Unit :=
  unless !run.isEmpty && run.length ≤ 100 && run.toList.all (fun c =>
      c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_')) do
    throw (IO.userError "Run id must contain 1–100 ASCII letters, digits, '-' or '_'")

def withDb (config : Config) (body : LeanLinq.Pg.Conn → IO α) : IO α := do
  let conn ← LeanLinq.Pg.connect config.db.connection
  try body conn finally conn.close

/-- The immutable run definition is also the durable publication intent.
Retry submission with the same definition until `submitted` is recorded.
A lost publish reply may duplicate the root; no database queue is used. -/
def submit (config : Config) (run : String) (definition : RunDefinition) : IO Unit := do
  validateRun run
  withDb config fun conn => do
    Postgres.initializeSchema conn
    unless ← Postgres.put conn run "definition" (toJson definition) do
      throw (IO.userError "Run id already belongs to a different workflow or input")
    if (← Postgres.get conn run "submitted").isSome then return
    let queue ← RabbitMQ.acquire config.queue run (create := true) (consume := false)
    try
      queue.enqueue Location.root
      unless ← Postgres.put conn run "submitted" (toJson true) do
        throw (IO.userError "Could not record confirmed submission")
    finally queue.close

def loadRun (config : Config) (run : String) : IO RunDefinition := do
  validateRun run
  withDb config fun conn => do
    let some value ← Postgres.get conn run "definition"
      | throw (IO.userError "Run does not exist; submit it first")
    match fromJson? value with
    | .ok definition => return definition
    | .error _ => throw (IO.userError "Invalid run definition")

def completed (config : Config) (run : String) : IO (Option Exit) :=
  withDb config fun conn => do
    let some value ← Postgres.get conn run Worker.completionKey | return none
    match fromJson? value with
    | .ok outcome => return some outcome
    | .error _ => throw (IO.userError "Invalid completion record")

def connectors (run : String) : Worker.Connectors Postgres.Config RabbitMQ.Config S3.Config RabbitMQ.Receipt where
  db config := Postgres.connect config run
  queue config := RabbitMQ.connect config run
  blobs := S3.connect

end LeanCloudRuntime
