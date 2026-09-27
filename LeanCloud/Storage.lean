import LeanCloud.Control

namespace LeanCloud
open Lean

/-- Storage operations thread a state `σ`. A model can update an in-memory map;
real backends can keep the same connection handle while performing effects in `m`.
`get`/`put` access execution records; writes may replace partial results and return
true when accepted. Blob operations report failures as `CloudError`; the backend
owns blob keys and validates references when reading immutable bytes. -/
structure Storage (σ : Type) (m : Type → Type) where
  get : String → StateT σ m (Option Json)
  put : String → Json → StateT σ m Bool
  putBlob : ByteArray → ExceptT CloudError (StateT σ m) BlobRef
  readBlob : BlobRef → ExceptT CloudError (StateT σ m) ByteArray
  resolveBlob : String → ExceptT CloudError (StateT σ m) BlobRef

/-- Execute a primitive operation. Base-monad failures retain the behavior of `m`. -/
def Storage.execute {σ : Type} {m : Type → Type} {α : Type} [Monad m]
    (storage : Storage σ m) (request : Operation m α) : ExceptT CloudError (StateT σ m) α :=
  match request with
  | .exec _ body => liftM (body ())
  | .putBlob bytes => storage.putBlob bytes
  | .readBlob ref => storage.readBlob ref
  | .resolveBlob name => storage.resolveBlob name

end LeanCloud
