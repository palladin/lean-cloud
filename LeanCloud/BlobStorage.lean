import LeanCloud.Control

universe u

namespace LeanCloud

/-- User-visible blob operations. Return ordinary failures as Cloud errors;
IO adapters use `captureIO` to include IO exceptions. This interface has no access
to interpreter records. The backend owns blob keys and validates references. -/
structure BlobStorage (m : Type → Type u) where
  putBlob : ByteArray → ExceptT CloudError m BlobRef
  readBlob : BlobRef → ExceptT CloudError m ByteArray
  resolveBlob : String → ExceptT CloudError m BlobRef

/-- Execute a user operation whose adapter returns failures as Cloud errors.
The interpreter records both success and failure before continuing. -/
def BlobStorage.execute {m : Type → Type u} {α : Type} [Monad m]
    (blobs : BlobStorage m) (request : Operation m α) (environment : Environment := {}) : ExceptT CloudError m α :=
  match request with
  | .exec _ body => body environment
  | .putBlob bytes => blobs.putBlob bytes
  | .readBlob ref => blobs.readBlob ref
  | .resolveBlob name => blobs.resolveBlob name

end LeanCloud
