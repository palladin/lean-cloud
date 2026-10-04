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
  def eval {α : Type} {m : Type → Type u} [Monad m]
      (blobs : BlobStorage m) (program : Cloud m α) : ExceptT CloudError m α :=
    match program with
    | EffF.pure value => pure value
    | .impure request continuation => do
      let value ← evalControl blobs request
      evalContinuation blobs continuation value
  termination_by structural program

  def evalControl {α : Type} {m : Type → Type u} [Monad m]
      (blobs : BlobStorage m) (request : Control m α) : ExceptT CloudError m α :=
    match request with
    | .delay => pure ()
    | .fail error => throw error
    | .command _ operation => blobs.execute operation
    | .parallel _ _ branches => do
      let outcomes ← liftM (m := m)
        (Array.ofFnM fun index => (eval blobs (branches index)).run)
      match outcomes.mapM id with
      | .ok values => return values
      | .error error => throw error
  termination_by structural request

  def evalContinuation {α β : Type} {m : Type → Type u} [Monad m]
      (blobs : BlobStorage m) (continuation : ArrsF (Control m) α β) (value : α) :
      ExceptT CloudError m β :=
    match continuation with
    | .one k => eval blobs (k value)
    | .append first rest => do
      let next ← evalContinuation blobs first value
      evalContinuation blobs rest next
  termination_by structural continuation
end

end Internal

/-- Evaluate the original program directly, with no execution-step budget. -/
def interpret {ι α : Type} {m : Type → Type u} [Monad m]
    (blobs : BlobStorage m) (program : ι → Cloud m α) (input : ι) :
    ExceptT CloudError m α :=
  Internal.eval blobs (program input)

end LeanCloud.DirectInterpreter
