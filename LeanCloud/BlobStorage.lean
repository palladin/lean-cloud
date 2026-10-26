import LeanCloud.Execution

universe u v

namespace LeanCloud

/-- Immutable, run-scoped names for user results. Publish atomically selects
one reference and returns that reference on every retry. -/
structure BlobNames (m : Type → Type u) where
  read : String → m (Option BlobRef)
  publish : String → BlobRef → m BlobRef

/-- User blob capabilities. These ordinary monadic actions may run concurrently
inside `Cloud.exec`. They cannot access the replay journal. -/
structure BlobStorage (m : Type → Type u) where
  putBlob : ByteArray → m BlobRef
  readBlob : BlobRef → m ByteArray
  resolveBlob : String → m BlobRef
  names : Option (BlobNames m) := none

/-- Change how capability failures are represented at an execution boundary. -/
def BlobStorage.map (f : {α : Type} → m α → n α) (blobs : BlobStorage m) : BlobStorage n where
  putBlob bytes := f (blobs.putBlob bytes)
  readBlob ref := f (blobs.readBlob ref)
  resolveBlob name := f (blobs.resolveBlob name)
  names := blobs.names.map fun names => {
    read key := f (names.read key), publish key ref := f (names.publish key ref) }

def BlobStorage.readNamed [Monad m] [MonadCloudExec m] (blobs : BlobStorage m)
    (name : String) : m (Option BlobRef) :=
  match blobs.names with
  | some names => names.read name
  | none => MonadCloudExec.restore (throw ⟨.unsupported, "Named result storage is not configured"⟩)

def BlobStorage.publishNamed [Monad m] [MonadCloudExec m] (blobs : BlobStorage m)
    (name : String) (ref : BlobRef) : m BlobRef :=
  match blobs.names with
  | some names => names.publish name ref
  | none => MonadCloudExec.restore (throw ⟨.unsupported, "Named result storage is not configured"⟩)

def BlobStorage.putText (blobs : BlobStorage m) (text : String) : m BlobRef :=
  blobs.putBlob text.toUTF8

def BlobStorage.readText [Monad m] [MonadCloudExec m]
    (blobs : BlobStorage m) (ref : BlobRef) : m String := do
  let bytes ← blobs.readBlob ref
  match String.fromUTF8? bytes with
  | some text => pure text
  | none => MonadCloudExec.restore (throw ⟨.invalidUtf8, "Blob is not valid UTF-8"⟩)

def BlobStorage.readTextByName [Monad m] [MonadCloudExec m]
    (blobs : BlobStorage m) (name : String) : m String := do
  blobs.readText (← blobs.resolveBlob name)

end LeanCloud
