import Wiki.Storage
import LeanCloudRuntime.Program

namespace Wiki
open Lean LeanCloud LeanCloudRuntime

/-- Resolve storage inside each effect: the scheduler can reconstruct the same
program without connecting to user blobs or executing any analysis. -/
def programs (environment : IO ObjectStore) : Array RegisteredProgram := Id.run do
  let b := backendWith environment
  let prepareProgram : CloudProgram PrepareRequest Prepared := {
    name := "wiki-prepare", version := "v3"
    description := "Prepare reusable article shards from Wikipedia XML/bzip2 dumps"
    run := prepare b }
  let countProgram : CloudProgram CountRequest Counts := {
    name := "wiki-count", version := "v3"
    description := "Count vocabulary occurrences and matching articles across a dataset"
    run := count b }
  let grepProgram : CloudProgram GrepRequest GrepReport := {
    name := "wiki-grep", version := "v3"
    description := "Find articles containing literal text or a POSIX extended regex"
    run := grep b }
  return #[
    { prepareProgram.register with validate := fun j => (fromJson? j : Except String PrepareRequest) >>= (·.validate) },
    { countProgram.register with validate := fun j => (fromJson? j : Except String CountRequest) >>= (·.validate) },
    { grepProgram.register with validate := fun j => (fromJson? j : Except String GrepRequest) >>= (·.validate) }]

end Wiki
