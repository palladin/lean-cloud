import LeanCloud.Proofs.ReplayStep

/-! Equations connecting queue selection and completion to the actual replay
driver. These lemmas are used by finite execution segments. -/

namespace LeanCloud.Proofs.ReplayModel
open Lean ReplayInterpreter.Internal

def decodeExit [codec : Codec α] : Exit → Except CloudError α
  | .success value => (codec.decode value).mapError (fun message => ⟨.codec, message⟩)
  | .failure error => .error error
  | .cancelled _ => .error ⟨.unsupported, "Cancellation is not implemented yet"⟩

theorem decodeExit_encoded [codec : Codec α] (law : CodecLaw codec) (value : α) :
    decodeExit (.success (codec.encode value)) = .ok value := by
  simp [decodeExit, law value, Except.mapError]

theorem result_run [codec : Codec α] (outcome : Exit) (state : State) :
    (result (m := StateT State Id) (α := α) outcome).run state =
      ((decodeExit outcome, state)) := by
  cases outcome with
  | success value =>
    cases decoded : codec.decode value <;> simp [result, decode, decodeExit, decoded] <;> rfl
  | failure error => rfl
  | cancelled reason => rfl

end LeanCloud.Proofs.ReplayModel
