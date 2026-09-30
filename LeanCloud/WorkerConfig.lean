import Lean.Data.Json

namespace LeanCloud
open Lean

/-- Connection settings supplied by the selected adapters. For example, a
database adapter can require a file path or a connection string, while a cloud
adapter can use an endpoint and an identity. Configuration contains no live
connections or interpreter state. -/
structure WorkerConfig (dbConfig queueConfig blobConfig : Type) where
  db : dbConfig
  queue : queueConfig
  blobs : blobConfig
  deriving FromJson, ToJson

namespace WorkerConfig

/-- Load the three typed adapter configurations. Do not include configuration
contents in parse errors: connection settings may contain credentials. Adapters
are responsible for validating their settings and resolving credentials. -/
def load [FromJson d] [FromJson q] [FromJson b] (path : System.FilePath) :
    IO (WorkerConfig d q b) := do
  let text ← IO.FS.readFile path
  let parsed := Json.parse text >>= fromJson? (α := WorkerConfig d q b)
  match parsed with
  | .ok config => return config
  | .error _ => throw (IO.userError "Invalid worker configuration")

end WorkerConfig
end LeanCloud
