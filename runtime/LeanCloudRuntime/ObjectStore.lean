import LeanCloud.Worker
import LeanCloudRuntime.Digest

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
  /-- Immutable content-addressed bytes. Existing content is trusted by SHA-256;
  this path never downloads an existing object to compare its contents. -/
  putContent : String → ByteArray → IO Unit
  size : String → IO (Option Nat)
  list : String → IO (Array String)
  erase : String → IO Unit

namespace ObjectStore

private abbrev digest := Digest.bytes

private def writeImmutable (store : ObjectStore) (key : String) (bytes : ByteArray) : IO Unit := do
  unless (← store.create key bytes) == bytes do
    throw (IO.userError "Immutable object conflicts with existing contents")

def putBytes (store : ObjectStore) (bytes : ByteArray) : IO BlobRef := do
  let (hash, checksum) ← Digest.fingerprint bytes
  let key := "objects/" ++ hash
  store.putContent key bytes
  return ⟨key, bytes.size, checksum⟩

private def validateRef (ref : BlobRef) : Except CloudError String := do
  let hash := ref.key.drop 8 |>.toString
  unless ref.key.startsWith "objects/" && hash.length == 64 && hash.toList.all (fun c =>
      c.isDigit || ('a' ≤ c && c ≤ 'f')) do throw ⟨.integrity, "Invalid blob reference"⟩
  return hash

def readBytes (store : ObjectStore) (ref : BlobRef) : ExceptT CloudError IO ByteArray := do
  let hash ← ExceptT.mk (pure (validateRef ref))
  let some bytes ← store.read ref.key | throw ⟨.missingBlob, "Blob is missing"⟩
  unless bytes.size == ref.size do throw ⟨.integrity, "Blob size does not match reference"⟩
  let (actual, checksum) ← Digest.fingerprint bytes
  unless checksum == ref.checksum && actual == hash do
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

def executionContext (store : ObjectStore) : ExecContext IO where
  cancellation := .never
  progress := .ignore
  queues := .unsupported
  blobs := {
    putBlob bytes := captureIO (liftM (store.putBytes bytes))
    readBlob ref := captureIO (store.readBytes ref)
    resolveBlob name := captureIO (store.resolve name) }

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

/-- User names cannot address interpreter or coordination records. They share
the run's cleanup lifetime, while referenced content-addressed blobs are shared. -/
def executionContextFor (store : ObjectStore) (run : String) : ExecContext IO :=
  { store.executionContext with blobs.names := some {
    read name := captureIO do
      let value ← store.readJson run ("user/blob/" ++ name)
      value.mapM fun json => liftM (IO.ofExcept (fromJson? json))
    publish name ref := captureIO do
      discard <| ExceptT.mk (pure (validateRef ref))
      let some size ← store.size ref.key | throw ⟨.missingBlob, "Blob is missing"⟩
      unless size == ref.size do throw ⟨.integrity, "Blob size does not match reference"⟩
      liftM (IO.ofExcept (fromJson? (← store.createJson run ("user/blob/" ++ name) (toJson ref)))) } }

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
