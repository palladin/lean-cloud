import Wiki.Storage

namespace Wiki.Import
open LeanCloudRuntime

/-- Copy exactly this many bytes; each compressed part starts/ends on a stream
boundary supplied by the index. Memory is bounded independently of dump size. -/
private def copy (input output : IO.FS.Handle) (size : Nat) : IO Unit := do
  let mut remaining := size
  while remaining > 0 do
    let bytes ← input.read (min remaining Files.chunkSize).toUSize
    if bytes.isEmpty then throw (IO.userError "Dump ended before indexed boundary")
    output.write bytes
    remaining := remaining - bytes.size
  output.flush

/-- Plan coarse groups of streams, never individual page jobs. Repeated offsets
are expected: many page entries refer to the same compressed stream. -/
def boundaries (index : System.FilePath) (size target : Nat) : IO (Array Nat) := do
  unless size > 0 && target > 0 && target ≤ maxPartBytes do throw (IO.userError "Invalid dump or part size")
  let handle ← IO.FS.Handle.mk index .read
  let mut result := #[0]
  let mut previous := 0
  let mut entries := 0
  repeat
    let line ← handle.getLine
    if line.isEmpty then break
    unless line.utf8ByteSize ≤ 16384 do throw (IO.userError "Oversized index line")
    let fields := line.splitOn ":"
    unless fields.length ≥ 3 do throw (IO.userError "Expected offset:page-id:title index")
    let some offset := fields[0]!.toNat? | throw (IO.userError "Invalid stream offset")
    unless fields[1]!.toNat?.isSome && previous ≤ offset && offset < size do
      throw (IO.userError "Invalid or unordered dump index")
    previous := offset
    entries := entries + 1
    if offset - result.back! ≥ target then
      result := result.push offset
      unless result.size ≤ maxParts do throw (IO.userError "Too many dump parts")
  unless entries > 0 do throw (IO.userError "Empty dump index")
  return result.push size

def multistream (store : ObjectStore) (dump index : System.FilePath)
    (target : Nat := 16 * MiB) : IO PrepareRequest := IO.FS.withTempDir fun directory => do
  let index ← if index.extension == some "bz2" then do
    let path := directory / "index.txt"
    Native.decompress index.toString path.toString
    pure path
  else pure index
  let size := (← dump.metadata).byteSize.toNat
  let offsets ← boundaries index size target
  let input ← IO.FS.Handle.mk dump .read
  let mut parts := #[]
  for i in [:offsets.size - 1] do
    let size := offsets[i+1]! - offsets[i]!
    unless size ≤ maxPartBytes do throw (IO.userError "A compressed group exceeds 256 MiB; use a smaller part target")
    let file ← IO.FS.withTempFile fun output path => do
      copy input output size
      Files.upload store path maxPartBytes
    parts := parts.push { file, compressed := true, first := i == 0, last := i + 2 == offsets.size : Part }
  unless (← input.read 1).isEmpty do throw (IO.userError "Dump grew during import")
  let source ← Files.putJson store ({ label := dump.fileName.getD "Wikipedia", parts } : Source)
  return { source }

/-- Convenience for a small complete XML fixture or a single bounded bz2 dump. -/
def document (store : ObjectStore) (dump : System.FilePath) : IO PrepareRequest := do
  let file ← Files.upload store dump maxPartBytes
  let source ← Files.putJson store ({
    label := dump.fileName.getD "Wikipedia"
    parts := #[{ file, compressed := dump.extension == some "bz2", first := true, last := true }] } : Source)
  return { source }

end Wiki.Import
