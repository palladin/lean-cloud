import LeanCloud.Execution

universe u v

namespace LeanCloud

/-- User blob capabilities. These ordinary monadic actions may run concurrently
inside `Cloud.exec`. They cannot access the replay journal. -/
structure BlobStorage (m : Type → Type u) where
  putBlob : ByteArray → m BlobRef
  readBlob : BlobRef → m ByteArray
  resolveBlob : String → m BlobRef

/-- Change how capability failures are represented at an execution boundary. -/
def BlobStorage.map (f : {α : Type} → m α → n α) (blobs : BlobStorage m) : BlobStorage n where
  putBlob bytes := f (blobs.putBlob bytes)
  readBlob ref := f (blobs.readBlob ref)
  resolveBlob name := f (blobs.resolveBlob name)

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
