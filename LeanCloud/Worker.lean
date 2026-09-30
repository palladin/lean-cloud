import LeanCloud.WorkerConfig
import LeanCloud.ReplayInterpreter
import LeanCloud.JournalDb
import LeanCloud.LeaseQueue

/-! Connection setup for a worker assigned to an existing workflow run.
Adapters locate the services; the existing interpreter executes the workflow.
Starting or restarting a worker neither seeds work nor resets durable state. -/

namespace LeanCloud.Worker
open Lean

/-- One acquired service handle. Closing releases this worker's resources, not
the durable service. Queue close must leave unacknowledged work recoverable. -/
structure Connection (α : Type) where
  service : α
  close : IO Unit

/-- Release a successfully acquired connection on return or IO failure. Nested
uses also release earlier connections when a later connection fails to open.
If opening itself fails, the connector must clean up its partial acquisition. -/
def Connection.use (openConnection : IO (Connection α)) (body : α → IO β) : IO β := do
  let connection ← openConnection
  try body connection.service
  finally connection.close

/-- Adapters capture their connection handles in the existing interfaces, so
the threaded backend state is `Unit`. The lease adapter adds the worker's own
delivery receipt. Each call must acquire independently owned worker resources.

Db and queue configurations must select the SAME existing run. Db keys are
relative to that run; blobs may be shared by multiple runs. The Db connection
exposes raw journal records, before `JournalDb.ofDb` is applied. Opening services
must not clear records, enqueue a root, or initialize a workflow. -/
structure Connectors (dbConfig queueConfig blobConfig receipt : Type) where
  db : dbConfig → IO (Connection (Db Unit IO))
  queue : queueConfig → IO (Connection (LeaseQueue Unit IO receipt))
  blobs : blobConfig → IO (Connection (BlobStorage Unit IO))

/-- Reserved physical key, distinct from location/result, fork, and child keys.
It shares the raw Db's run namespace and survives worker restarts. -/
def completionKey : String := "completed"

private def readCompleted (db : Db Unit IO) : StateT Unit IO (Option Exit) := do
  let some value ← db.get completionKey | return none
  match fromJson? value with
  | .ok outcome => return some outcome
  | .error _ => throw (IO.userError "Invalid workflow completion record")

private def writeCompleted (db : Db Unit IO) (outcome : Exit) : StateT Unit IO Unit := do
  unless ← JournalDb.putSame db completionKey (toJson outcome) do
    throw (IO.userError "Db rejected workflow completion record")

/-- Connect to the configured services, run the existing interpreter, and close
all connections. `program` and `input` must be the same on every worker assigned
to this run. Submission and entry-point/version selection belong to the caller.

Workflow outcomes (including fuel exhaustion) are returned as `Except`.
Connection, transport, and storage failures escape through IO for the process
supervisor to handle. There is no hidden restart loop or workflow initialization.
The journal's same-value writer assumption still applies to overlapping writes.
Adapters own dequeue waiting, lease renewal, and durable publication. -/
def run [Codec α] (connectors : Connectors d q b ρ) (config : WorkerConfig d q b)
    (fuel : Nat) (program : ι → Cloud IO α) (input : ι) : IO (Except CloudError α) :=
  Connection.use (connectors.db config.db) fun rawDb =>
  Connection.use (connectors.blobs config.blobs) fun blobs =>
  Connection.use (connectors.queue config.queue) fun transport => do
    let db := LeaseQueue.db (JournalDb.ofDb rawDb)
    let queue := transport.toWorkQueue (readCompleted rawDb) (writeCompleted rawDb)
    let (outcome, _) ←
      (interpret db (LeaseQueue.blobs blobs) queue fuel program input).run ⟨(), none⟩
    return outcome

end LeanCloud.Worker
