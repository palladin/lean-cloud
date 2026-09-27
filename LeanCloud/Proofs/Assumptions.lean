import LeanCloud.Core

/-! Assumptions for the first interpreter-equivalence theorem. These predicates
describe programs without changing the runtime effect algebra or codecs. -/

namespace LeanCloud.Proofs
open LeanEff

/-- Persisting and recovering a value must return that exact value. The explicit
codec argument also covers codecs carried inside control requests. -/
def CodecLaw (codec : Codec α) : Prop :=
  ∀ value, codec.decode (codec.encode value) = .ok value

mutual
  /-- The fragment covered by the first equivalence theorem. All embedded codecs
  must round-trip, and choice is excluded. Continuations are checked for every
  possible argument, not just arguments reached in one particular execution. -/
  def Supported {m : Type → Type} {α : Type} (program : Cloud m α) : Prop :=
    match program with
    | .pure _ => True
    | .impure request continuation =>
      SupportedControl request ∧ SupportedContinuation continuation
  termination_by structural program

  def SupportedControl {m : Type → Type} {α : Type} (request : Control m α) : Prop :=
    match request with
    | .delay => True
    | .fail _ => True
    | .sequential codec _ => CodecLaw codec
    | .parallel codec _ branches => CodecLaw codec ∧ ∀ index, Supported (branches index)
    | .choice .. => False
  termination_by structural request

  def SupportedContinuation {m : Type → Type} {α β : Type}
      (continuation : ArrsF (Control m) α β) : Prop :=
    match continuation with
    | .one k => ∀ value, Supported (k value)
    | .append first rest => SupportedContinuation first ∧ SupportedContinuation rest
  termination_by structural continuation
end

end LeanCloud.Proofs
