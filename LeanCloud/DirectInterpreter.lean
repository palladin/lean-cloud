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
      (context : ExecContext m) (program : Cloud m α) : ExceptT CloudError m α :=
    match program with
    | EffF.pure _ value => pure value
    | .impure _ request continuation => do
      let value ← evalControl context request
      evalContinuation context continuation value
  termination_by structural program

  def evalControl {α : Type} {m : Type → Type u} [Monad m]
      (context : ExecContext m) (request : Control m α) : ExceptT CloudError m α :=
    match request with
    | .delay => pure ()
    | .fail error => throw error
    | .command _ _ body => body context
    | .parallel _ _ branches _ => do
      -- Run every child, keeping failures as values so they cannot skip later children.
      let outcomes ← liftM (m := m)
        (Array.ofFnM fun index => (eval context (branches index)).run)
      -- Preserve array order and select the first error only after all children ran.
      match outcomes.mapM id with
      | .ok values => return values
      | .error error => throw error
  termination_by structural request

  /-- Interpret lean-eff's queue of binds from left to right. Keeping the queue
  explicit makes evaluation structurally recursive, without a fuel parameter. -/
  def evalContinuation {α β : Type} {m : Type → Type u} [Monad m]
      (context : ExecContext m) (continuation : ArrsF (Control m) SourceSiteId α β) (value : α) :
      ExceptT CloudError m β :=
    match continuation with
    | .one k => eval context (k value)
    | .append first rest => do
      let next ← evalContinuation context first value
      evalContinuation context rest next
  termination_by structural continuation
end

end Internal

/-- Evaluate the original program directly, with no execution-step budget. -/
def interpret {ι α : Type} {m : Type → Type u} [Monad m]
    (context : ExecContext m) (program : ι → Cloud m α) (input : ι) :
    ExceptT CloudError m α :=
  Internal.eval context (program input)

end LeanCloud.DirectInterpreter
