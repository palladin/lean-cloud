import LeanEff.Core
import LeanCloud.Protocol
import LeanCloud.Execution
import LeanCloud.SourceInfo
import LeanCloud.Environment
import LeanCloud.ParallelLabel

universe u

namespace LeanCloud
open Lean LeanEff

/-- Higher-order cloud effects carry local computations directly to the worker handler. -/
inductive Control (m : Type → Type u) : Type → Type (max 1 u) where
  | delay : Control m Unit
  | fail {α : Type} : CloudError → Control m α
  | parallel {α : Type} (codec : Codec α) (count : Nat)
      (branches : Fin count → EffF (Control m) SourceSiteId α)
      (label : ParallelLabel := {}) : Control m (Array α)
  | command {α : Type} (codec : Codec α) (label : String)
      (body : ExecContext m → ExceptT CloudError m α) : Control m α

end LeanCloud
