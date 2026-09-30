import LeanCloud.Control

universe u

namespace LeanCloud

/-- User-visible blob operations. This interface has no access to interpreter
records. The backend owns blob keys and validates references when reading bytes. -/
structure BlobStorage (σ : Type) (m : Type → Type u) where
  putBlob : ByteArray → ExceptT CloudError (StateT σ m) BlobRef
  readBlob : BlobRef → ExceptT CloudError (StateT σ m) ByteArray
  resolveBlob : String → ExceptT CloudError (StateT σ m) BlobRef

/-- Execute a user operation. Base-monad failures retain the behavior of `m`. -/
def BlobStorage.execute {σ : Type} {m : Type → Type u} {α : Type} [Monad m]
    (blobs : BlobStorage σ m) (request : Operation m α) : ExceptT CloudError (StateT σ m) α :=
  match request with
  | .exec _ body => liftM (body ())
  | .putBlob bytes => blobs.putBlob bytes
  | .readBlob ref => blobs.readBlob ref
  | .resolveBlob name => blobs.resolveBlob name

end LeanCloud
