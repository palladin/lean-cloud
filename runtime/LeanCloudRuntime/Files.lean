import LeanCloudRuntime.Storage
import LeanCloudRuntime.Parallel

namespace LeanCloudRuntime
open Lean LeanCloud LeanCloudRuntime

/-- A file is an immutable manifest of content-addressed blob chunks. Only this
reference enters the workflow journal; file contents never do. -/
structure FileRef where
  manifest : BlobRef
  size : Nat
  sha256 : String
  deriving Repr, BEq, ToJson, FromJson

instance : Inhabited FileRef := ⟨⟨⟨"", 0, 0⟩, 0, ""⟩⟩

def FileRef.validate (ref : FileRef) : Except String Unit := do
  let isHash (value : String) := value.length == 64 && value.toList.all (fun c =>
    c.isDigit || ('a' ≤ c && c ≤ 'f'))
  unless isHash ref.sha256 && ref.manifest.key.startsWith "objects/" &&
      isHash (ref.manifest.key.drop 8).toString && ref.manifest.size ≤ 16 * 1024 * 1024 do
    throw "Invalid content-addressed file reference"

private structure FileManifest where
  format : String := "lean-cloud/file/v1"
  chunks : Array BlobRef
  size : Nat
  sha256 : String
  deriving ToJson, FromJson

namespace Files

def chunkSize : Nat := 4 * 1024 * 1024

def digest (path : System.FilePath) : IO String := do
  Digest.file path.toString

private def readBlob (store : ObjectStore) (ref : BlobRef) : IO ByteArray := do
  match ← (store.readBytes ref).run with
  | .ok bytes => return bytes
  | .error error => throw (IO.userError error.message)

/-- An authenticated chunk index. Partial reads verify every fetched chunk;
the whole-file digest is additionally checked by `download`. The cache holds
at most one chunk, independently of file size, and is safe for concurrent reads. -/
structure Reader where
  private mk ::
  private store : ObjectStore
  private chunks : Array BlobRef
  private ends : Array Nat
  private cache : Std.Mutex (Option (Nat × ByteArray))
  size : Nat

def openReader (store : ObjectStore) (ref : FileRef) : IO Reader := do
  IO.ofExcept ref.validate
  let bytes ← readBlob store ref.manifest
  let some text := String.fromUTF8? bytes | throw (IO.userError "Invalid file manifest encoding")
  let manifest : FileManifest ← IO.ofExcept (Json.parse text >>= fromJson?)
  unless manifest.format == "lean-cloud/file/v1" && manifest.size == ref.size &&
      manifest.sha256 == ref.sha256 &&
      manifest.chunks.all (fun chunk => 0 < chunk.size && chunk.size ≤ chunkSize) &&
      (manifest.chunks.foldl (fun total chunk => total + chunk.size) 0) == ref.size do
    throw (IO.userError "Invalid file manifest")
  let mut ends := #[]
  let mut total := 0
  for chunk in manifest.chunks do
    total := total + chunk.size
    ends := ends.push total
  return ⟨store, manifest.chunks, ends, ← Std.Mutex.new none, ref.size⟩

private def Reader.chunk (reader : Reader) (index : Nat) : IO ByteArray := do
  if let some (cached, bytes) ← reader.cache.atomically get then
    if cached == index then return bytes
  let some ref := reader.chunks[index]? | throw (IO.userError "Invalid chunk offset")
  let bytes ← readBlob reader.store ref
  reader.cache.atomically (set (some (index, bytes)))
  return bytes

/-- Seek through the manifest, fetching only intersecting chunks. `count` is
clipped to EOF; a short/corrupt/missing chunk throws instead of truncating data. -/
def Reader.read (reader : Reader) (offset count : Nat) : IO ByteArray := do
  let stop := min reader.size (offset + count)
  if offset ≥ stop then return {}
  let mut low := 0
  let mut high := reader.ends.size
  while low < high do
    let mid := (low + high) / 2
    if reader.ends[mid]! ≤ offset then low := mid + 1 else high := mid
  let mut index := low
  let mut position := offset
  let mut result := ByteArray.empty
  while position < stop do
    let start := if index == 0 then 0 else reader.ends[index - 1]!
    let bytes ← reader.chunk index
    let finish := min stop reader.ends[index]!
    result := result ++ bytes.extract (position - start) (finish - start)
    position := finish
    index := index + 1
  return result

/-- Commit the manifest last. A failed upload cannot publish a partial file.
Retrying uploads reuses immutable chunks. At most `max 1 concurrency` chunk buffers
are retained at once; transfers run in parallel but preserve chunk order.
The small chunk index grows with file size. -/
def upload (store : ObjectStore) (path : System.FilePath) (limit : Nat)
    (concurrency : Nat := 1) : IO FileRef := do
  let size := (← path.metadata).byteSize.toNat
  unless size ≤ limit do throw (IO.userError "File exceeds configured byte limit")
  let sha256 ← digest path
  let handle ← IO.FS.Handle.mk path .read
  let mut chunks := #[]
  let mut total := 0
  repeat
    let mut batch := #[]
    for _ in [:max 1 concurrency] do
      let bytes ← handle.read chunkSize.toUSize
      if bytes.isEmpty then break
      total := total + bytes.size
      unless total ≤ limit do throw (IO.userError "File grew beyond configured byte limit")
      batch := batch.push bytes
    if batch.isEmpty then break
    chunks := chunks ++ (← Parallel.map concurrency batch store.putBytes)
  unless total == size && (← digest path) == sha256 do
    throw (IO.userError "File changed during upload")
  let manifest : FileManifest := { chunks, size, sha256 }
  let ref ← store.putBytes (toJson manifest).compress.toUTF8
  return ⟨ref, size, sha256⟩

/-- The destination is exclusively owned by the caller (normally a temporary
workspace). Bounded batches fetch chunks concurrently and write them in order.
Hash and length checks cover both individual chunks and the file. -/
def download (store : ObjectStore) (ref : FileRef) (path : System.FilePath) (limit : Nat)
    (concurrency : Nat := 1) : IO Unit := do
  IO.ofExcept ref.validate
  unless ref.size ≤ limit && ref.manifest.size ≤ 16 * 1024 * 1024 do
    throw (IO.userError "File reference exceeds configured limit")
  let reader ← openReader store ref
  let handle ← IO.FS.Handle.mk path .write
  let width := max 1 concurrency
  let mut index := 0
  while index < reader.chunks.size do
    let batch ← Parallel.map width (reader.chunks.extract index (index + width)) (readBlob store)
    for bytes in batch do handle.write bytes
    index := index + width
  handle.flush
  unless (← digest path) == ref.sha256 do throw (IO.userError "File digest mismatch")
  -- On failure the caller's private workspace owns any partial file. In
  -- particular, do not remove a file owned by IO.FS.withTempFile's cleanup.


def putText (store : ObjectStore) (text : String) : IO FileRef :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr text
    handle.flush
    upload store path text.utf8ByteSize

def readText (store : ObjectStore) (ref : FileRef) (limit : Nat := 16 * 1024 * 1024) : IO String :=
  IO.FS.withTempFile fun _ path => do
    download store ref path limit
    IO.FS.readFile path

def metadataLimit : Nat := 256 * 1024 * 1024

def putJson [ToJson α] (store : ObjectStore) (value : α) : IO FileRef := do
  let text := (toJson value).pretty
  unless text.utf8ByteSize ≤ metadataLimit do throw (IO.userError "Artifact metadata exceeds 256 MiB")
  putText store text

def readJson [FromJson α] (store : ObjectStore) (ref : FileRef) : IO α := do
  IO.ofExcept (Json.parse (← readText store ref metadataLimit) >>= fromJson?)

end Files
end LeanCloudRuntime
