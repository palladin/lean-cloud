import LeanCloud.Core

/-! Codec laws and the supported program fragment. These predicates
describe programs without changing the runtime effect algebra or codecs. -/

universe u

namespace LeanCloud.Proofs
open LeanEff

/-- Persisting and recovering a value must return that exact value. The explicit
codec argument also covers codecs carried inside control requests. -/
def CodecLaw (codec : Codec α) : Prop :=
  ∀ value, codec.decode (codec.encode value) = .ok value

mutual
  /-- The supported fragment used by the direct-evaluation proofs. Parallel codecs must round-trip.
  Choice and user operations (exec and blobs) are excluded. Continuations are checked for every
  possible argument, not just arguments reached in one particular execution. -/
  def PureProgram {m : Type → Type u} {α : Type} (program : Cloud m α) : Prop :=
    match program with
    | EffF.pure _ => True
    | .impure request continuation =>
      PureControl request ∧ PureContinuation continuation
  termination_by structural program

  def PureControl {m : Type → Type u} {α : Type} (request : Control m α) : Prop :=
    match request with
    | .delay => True
    | .fail _ => True
    | .sequential .. => False
    | .parallel codec _ branches => CodecLaw codec ∧ ∀ index, PureProgram (branches index)
    | .choice .. => False
  termination_by structural request

  def PureContinuation {m : Type → Type u} {α β : Type}
      (continuation : ArrsF (Control m) α β) : Prop :=
    match continuation with
    | .one k => ∀ value, PureProgram (k value)
    | .append first rest => PureContinuation first ∧ PureContinuation rest
  termination_by structural continuation
end

end LeanCloud.Proofs
