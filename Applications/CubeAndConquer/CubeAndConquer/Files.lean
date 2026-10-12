import LeanCloudRuntime.Storage

namespace CubeAndConquer
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
  let out ← IO.Process.output { cmd := "openssl", args := #["dgst", "-sha256", "-r", path.toString] }
  let hash := (out.stdout.splitOn " ").head!
  unless out.exitCode == 0 && hash.length == 64 && hash.toList.all (fun c =>
      c.isDigit || ('a' ≤ c && c ≤ 'f')) do throw (IO.userError "File SHA-256 failed")
  return hash

private def readBlob (store : ObjectStore) (ref : BlobRef) : IO ByteArray := do
  match ← (store.readBytes ref).run with
  | .ok bytes => return bytes
  | .error error => throw (IO.userError error.message)

/-- Commit the manifest last. A failed upload cannot publish a partial file.
Retrying uploads reuses immutable chunks. Data buffers are bounded by chunkSize;\nthe small chunk index grows with file size. -/
def upload (store : ObjectStore) (path : System.FilePath) (limit : Nat) : IO FileRef := do
  let size := (← path.metadata).byteSize.toNat
  unless size ≤ limit do throw (IO.userError "File exceeds configured byte limit")
  let sha256 ← digest path
  let handle ← IO.FS.Handle.mk path .read
  let mut chunks := #[]
  let mut total := 0
  repeat
    let bytes ← handle.read chunkSize.toUSize
    if bytes.isEmpty then break
    total := total + bytes.size
    unless total ≤ limit do throw (IO.userError "File grew beyond configured byte limit")
    chunks := chunks.push (← store.putBytes bytes)
  unless total == size && (← digest path) == sha256 do
    throw (IO.userError "File changed during upload")
  let manifest : FileManifest := { chunks, size, sha256 }
  let ref ← store.putBytes (toJson manifest).compress.toUTF8
  return ⟨ref, size, sha256⟩

/-- The destination is exclusively owned by the caller (normally a temporary
workspace). Hash and length checks cover both individual chunks and the file. -/
def download (store : ObjectStore) (ref : FileRef) (path : System.FilePath) (limit : Nat) : IO Unit := do
  IO.ofExcept ref.validate
  unless ref.size ≤ limit && ref.manifest.size ≤ 16 * 1024 * 1024 do
    throw (IO.userError "File reference exceeds configured limit")
  let bytes ← readBlob store ref.manifest
  let some text := String.fromUTF8? bytes | throw (IO.userError "Invalid file manifest encoding")
  let manifest : FileManifest ← IO.ofExcept (Json.parse text >>= fromJson?)
  unless manifest.format == "lean-cloud/file/v1" && manifest.size == ref.size &&
      manifest.sha256 == ref.sha256 &&
      manifest.chunks.all (fun chunk => 0 < chunk.size && chunk.size ≤ chunkSize) &&
      (manifest.chunks.foldl (fun total chunk => total + chunk.size) 0) == ref.size do
    throw (IO.userError "Invalid file manifest")
  let handle ← IO.FS.Handle.mk path .write
  for chunk in manifest.chunks do handle.write (← readBlob store chunk)
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
end CubeAndConquer
