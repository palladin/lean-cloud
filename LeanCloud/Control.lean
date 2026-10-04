import LeanEff.Core
import LeanCloud.Protocol
import LeanCloud.SourceInfo

universe u

namespace LeanCloud
open Lean LeanEff

/-- Primitive operations executed directly or recorded and replayed at a location. -/
inductive Operation (m : Type → Type u) : Type → Type (max 1 u) where
  | exec {α : Type} (label : String) (body : Unit → m α) : Operation m α
  | putBlob (bytes : ByteArray) : Operation m BlobRef
  | readBlob (ref : BlobRef) : Operation m ByteArray
  | resolveBlob (name : String) : Operation m BlobRef

/-- Higher-order cloud effects carry local computations directly to the worker handler. -/
inductive Control (m : Type → Type u) : Type → Type (max 1 u) where
  | delay : Control m Unit
  | fail {α : Type} : CloudError → Control m α
  | parallel {α : Type} (codec : Codec α) (count : Nat) :
      (Fin count → EffF (Control m) SourceSiteId α) → Control m (Array α)
  | command {α : Type} (codec : Codec α) (operation : Operation m α) : Control m α

end LeanCloud
