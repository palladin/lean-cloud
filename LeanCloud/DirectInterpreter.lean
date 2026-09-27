import LeanCloud.Core
import LeanCloud.Storage

/-! Direct sequential semantics, defined by mutual structural recursion over
computations, control requests, and continuation queues. No replay or result codecs
are used. Parallel evaluates all children in array order before selecting an error. -/

namespace LeanCloud.DirectInterpreter
open LeanEff

mutual
  private def eval {σ α : Type} {m : Type → Type} [Monad m]
      (storage : Storage σ m) (program : Cloud m α) : ExceptT CloudError (StateT σ m) α :=
    match program with
    | .pure value => pure value
    | .impure request continuation => do
      let value ← evalControl storage request
      evalContinuation storage continuation value
  termination_by structural program

  private def evalControl {σ α : Type} {m : Type → Type} [Monad m]
      (storage : Storage σ m) (request : Control m α) : ExceptT CloudError (StateT σ m) α :=
    match request with
    | .delay => pure ()
    | .fail error => throw error
    | .sequential _ operation => storage.execute operation
    | .choice .. => throw ⟨.unsupported, "Choice is not implemented yet"⟩
    | .parallel _ _ branches => do
      let outcomes ← liftM (m := StateT σ m)
        (Array.ofFnM fun index => (eval storage (branches index)).run)
      match outcomes.mapM id with
      | .ok values => return values
      | .error error => throw error
  termination_by structural request

  private def evalContinuation {σ α β : Type} {m : Type → Type} [Monad m]
      (storage : Storage σ m) (continuation : ArrsF (Control m) α β) (value : α) :
      ExceptT CloudError (StateT σ m) β :=
    match continuation with
    | .one k => eval storage (k value)
    | .append first rest => do
      let next ← evalContinuation storage first value
      evalContinuation storage rest next
  termination_by structural continuation
end

/-- Evaluate the original program directly, with no execution-step budget. -/
def interpret {σ ι α : Type} {m : Type → Type} [Monad m]
    (storage : Storage σ m) (program : ι → Cloud m α) (input : ι) :
    ExceptT CloudError (StateT σ m) α :=
  eval storage (program input)

end LeanCloud.DirectInterpreter
