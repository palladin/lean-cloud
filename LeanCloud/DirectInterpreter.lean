import LeanCloud.Core
import LeanCloud.BlobStorage

/-! Direct sequential semantics, defined by mutual structural recursion over
computations, control requests, and continuation queues. No replay or result codecs
are used. Parallel evaluates all children in array order before selecting an error. -/

universe u

namespace LeanCloud.DirectInterpreter
open LeanEff

-- Stable internal names allow semantic proofs to live in a separate module.
namespace Internal

mutual
  /-- A value finishes evaluation; an effect supplies the value for its continuation. -/
  def eval {α : Type} {m : Type → Type u} [Monad m]
      (blobs : BlobStorage m) (program : Cloud m α) (environment : Environment := {}) : ExceptT CloudError m α :=
    match program with
    | EffF.pure _ value => pure value
    | .impure _ request continuation => do
      let value ← evalControl blobs request environment
      evalContinuation blobs continuation value environment
  termination_by structural program

  def evalControl {α : Type} {m : Type → Type u} [Monad m]
      (blobs : BlobStorage m) (request : Control m α) (environment : Environment := {}) : ExceptT CloudError m α :=
    match request with
    | .delay => pure ()
    | .fail error => throw error
    | .command _ operation => blobs.execute operation environment
    | .parallel _ _ branches => do
      -- Run every child, keeping failures as values so they cannot skip later children.
      let outcomes ← liftM (m := m)
        (Array.ofFnM fun index => (eval blobs (branches index) environment).run)
      -- Preserve array order and select the first error only after all children ran.
      match outcomes.mapM id with
      | .ok values => return values
      | .error error => throw error
  termination_by structural request

  /-- Interpret lean-eff's queue of binds from left to right. Keeping the queue
  explicit makes evaluation structurally recursive, without a fuel parameter. -/
  def evalContinuation {α β : Type} {m : Type → Type u} [Monad m]
      (blobs : BlobStorage m) (continuation : ArrsF (Control m) SourceSiteId α β) (value : α) (environment : Environment := {}) :
      ExceptT CloudError m β :=
    match continuation with
    | .one k => eval blobs (k value) environment
    | .append first rest => do
      let next ← evalContinuation blobs first value environment
      evalContinuation blobs rest next environment
  termination_by structural continuation
end

end Internal

/-- Evaluate the original program directly, with no execution-step budget. -/
def interpret {ι α : Type} {m : Type → Type u} [Monad m]
    (blobs : BlobStorage m) (program : ι → Cloud m α) (input : ι) (environment : Environment := {}) :
    ExceptT CloudError m α :=
  Internal.eval blobs (program input) environment

end LeanCloud.DirectInterpreter
