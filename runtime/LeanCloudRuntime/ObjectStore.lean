import LeanCloud.Worker

namespace LeanCloudRuntime
open Lean LeanCloud

/-- Provider boundary for durable objects. `create` atomically selects one value
and returns that value on every retry. `read` observes committed writes. `list`
returns a bounded first page under a prefix; empty means no matching objects.
Transport failures are IO exceptions, never missing data. The user-blob adapter
converts them to workflow failures; journal/coordination callers leave them outside
the user-effect boundary. -/
structure ObjectStore where
  ensureContainer : IO Unit
  read : String → IO (Option ByteArray)
  create : String → ByteArray → IO ByteArray
  list : String → IO (Array String)
  erase : String → IO Unit

namespace ObjectStore

private def digest (bytes : ByteArray) : IO String := IO.FS.withTempFile fun handle path => do
  handle.write bytes
  handle.flush
  let result ← IO.Process.output { cmd := "openssl", args := #["dgst", "-sha256", "-r", path.toString] }
  let hash := (result.stdout.splitOn " ").head!
  unless result.exitCode == 0 && hash.length == 64 && hash.toList.all (fun c =>
      c.isDigit || ('a' ≤ c && c ≤ 'f')) do throw (IO.userError "SHA-256 computation failed")
  return hash

private def writeImmutable (store : ObjectStore) (key : String) (bytes : ByteArray) : IO Unit := do
  unless (← store.create key bytes) == bytes do
    throw (IO.userError "Immutable object conflicts with existing contents")

def putBytes (store : ObjectStore) (bytes : ByteArray) : IO BlobRef := do
  let key := "objects/" ++ (← digest bytes)
  writeImmutable store key bytes
  return ⟨key, bytes.size, modelChecksum bytes⟩

def readBytes (store : ObjectStore) (ref : BlobRef) : ExceptT CloudError IO ByteArray := do
  let hash := ref.key.drop 8 |>.toString
  unless ref.key.startsWith "objects/" && hash.length == 64 && hash.toList.all (fun c =>
      c.isDigit || ('a' ≤ c && c ≤ 'f')) do throw ⟨.integrity, "Invalid blob reference"⟩
  let some bytes ← store.read ref.key | throw ⟨.missingBlob, "Blob is missing"⟩
  unless bytes.size == ref.size && modelChecksum bytes == ref.checksum && (← digest bytes) == hash do
    throw ⟨.integrity, "Blob contents do not match reference"⟩
  return bytes

/-- Names are hashed into flat keys. The original name detects mismatched data. -/
def name (store : ObjectStore) (name : String) (ref : BlobRef) : IO Unit := do
  writeImmutable store ("names/" ++ (← digest name.toUTF8)) (toJson (name, ref)).compress.toUTF8

def resolve (store : ObjectStore) (name : String) : ExceptT CloudError IO BlobRef := do
  let some bytes ← store.read ("names/" ++ (← digest name.toUTF8))
    | throw ⟨.missingBlob, "Blob name is missing"⟩
  let some text := String.fromUTF8? bytes | throw ⟨.codec, "Invalid blob name record"⟩
  match Json.parse text >>= fromJson? (α := String × BlobRef) with
  | .ok (storedName, ref) =>
    unless storedName == name do throw ⟨.integrity, "Blob name record does not match its key"⟩
    return ref
  | .error _ => throw ⟨.codec, "Invalid blob name record"⟩

def storage (store : ObjectStore) : BlobStorage IO where
  putBlob bytes := captureIO (liftM (store.putBytes bytes))
  readBlob ref := captureIO (store.readBytes ref)
  resolveBlob name := captureIO (store.resolve name)

def runPrefix (run : String) : Except String String := do
  unless !run.isEmpty && run.length ≤ 100 && run.toList.all (fun c =>
      c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_')) do
    throw "Invalid run ID"
  return "runs/" ++ run ++ "/records/"

private def recordKey (run key : String) : IO String := do
  return (← IO.ofExcept (runPrefix run)) ++ (← digest key.toUTF8)

private def decodeRecord (key : String) (bytes : ByteArray) : IO Json := do
  let some text := String.fromUTF8? bytes | throw (IO.userError "Invalid record UTF-8")
  let (storedKey, value) ← IO.ofExcept (Json.parse text >>= fromJson? (α := String × Json))
  unless storedKey == key do throw (IO.userError "Record does not match its key")
  return value

def readJson (store : ObjectStore) (run key : String) : IO (Option Json) := do
  let some bytes ← store.read (← recordKey run key) | return none
  return some (← decodeRecord key bytes)

def createJson (store : ObjectStore) (run key : String) (value : Json) : IO Json := do
  let bytes ← store.create (← recordKey run key) (toJson (key, value)).compress.toUTF8
  decodeRecord key bytes

def records (store : ObjectStore) (run : String) : ReplayStore IO where
  read key := do
    let some value ← store.readJson run key | return none
    return some (← IO.ofExcept (fromJson? value))
  create key record := do
    IO.ofExcept (fromJson? (← store.createJson run key (toJson record)))

/-- Validate the entire page before deleting anything. Provider listings cannot
escape the retired run's namespace or reach shared user blobs and names. -/
def runRecordKeys (run : String) (keys : Array String) : Except String (Array String) := do
  let keyPrefix ← runPrefix run
  for key in keys do
    unless key.startsWith keyPrefix do throw "Listing escaped the run namespace"
    let hash := key.drop keyPrefix.length |>.toString
    unless hash.length == 64 && hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
      throw "Unexpected key in the run namespace"
  return keys

def isRemoved (store : ObjectStore) (run : String) : IO Bool := do
  let some bytes ← store.read ("removed/" ++ (← digest run.toUTF8)) | return false
  unless bytes == run.toUTF8 do throw (IO.userError "Cannot read run removal marker")
  return true

/-- Persist retirement, then repeatedly delete the first bounded page. Restarting
cleanup cannot skip records; the marker remains and IDs cannot be reused. -/
def removeRun (store : ObjectStore) (run : String) : IO Unit := do
  let keyPrefix ← IO.ofExcept (runPrefix run)
  writeImmutable store ("removed/" ++ (← digest run.toUTF8)) run.toUTF8
  repeat
    let keys ← IO.ofExcept (runRecordKeys run (← store.list keyPrefix))
    if keys.isEmpty then return
    for key in keys do store.erase key

end ObjectStore
end LeanCloudRuntime
