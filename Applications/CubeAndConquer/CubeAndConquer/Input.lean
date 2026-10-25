import CubeAndConquer.Files
import Std.Sync.Mutex

namespace CubeAndConquer.Input
open LeanCloudRuntime

-- One cache slot per worker process. Hold its lease until all local tasks have
-- joined, so another request cannot replace a CNF while solvers still read it.
private initialize lock : Std.Mutex Unit ← Std.Mutex.new ()

private def validFile (path : System.FilePath) (ref : FileRef) : IO Bool := do
  if !(← path.pathExists) then return false
  return (← path.metadata).byteSize.toNat == ref.size && (← Files.digest path) == ref.sha256

/-- Reuse one validated immutable input. A cache miss downloads to a private
pending file and publishes atomically; partial downloads are never cache hits.
The directory must be private to this worker process. -/
def withFile (store : ObjectStore) (cache : Option System.FilePath)
    (ref : FileRef) (limit concurrency : Nat)
    (action : System.FilePath → IO α) : IO α := do
  IO.ofExcept ref.validate
  unless ref.size ≤ limit do throw (IO.userError "CNF exceeds configured input limit")
  match cache with
  | none => IO.FS.withTempDir fun directory => do
      let path := directory / "original.cnf"
      Files.download store ref path limit concurrency
      action path
  | some directory => lock.atomically do
      IO.FS.createDirAll directory
      let path := directory / "original.cnf"
      if !(← validFile path ref) then
        -- Evict the previous input before downloading: persistent cache size is
        -- bounded by one input, independently of the number of submitted runs.
        if ← path.pathExists then IO.FS.removeFile path
        let pending := directory / "original.pending"
        try
          Files.download store ref pending limit concurrency
          IO.FS.rename pending path
        finally
          if ← pending.pathExists then IO.FS.removeFile pending
      action path

end CubeAndConquer.Input
