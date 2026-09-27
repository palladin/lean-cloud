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

theorem result_run [codec : Codec α] (outcome : Exit) (state : State) (world : World) :
    (result (m := StateT State (StateM World)) (α := α) outcome).run state world =
      ((decodeExit outcome, state), world) := by
  cases outcome with
  | success value =>
    cases decoded : codec.decode value <;> simp [result, decode, decodeExit, decoded] <;> rfl
  | failure error => rfl
  | cancelled reason => rfl

theorem run_selected [Codec α] (blobs : BlobModel World) (root : Cloud (StateM World) Json)
    (fuel : Nat) (journal : Journal) (location : Location) (rest : List Location)
    (world nextWorld : World) (nextState : State) (updateResult : StepResult)
    (executed : (step (storage blobs) (fuel + 1) root location).run ⟨journal, location :: rest, none⟩ world =
      ((.ok updateResult, nextState), nextWorld)) :
    (run (α := α) (storage blobs) queue (fuel + 1) root).run ⟨journal, location :: rest, none⟩ world =
      match updateResult with
      | .done outcome => ((decodeExit outcome, update nextState location updateResult), nextWorld)
      | .runnable _ =>
        (run (α := α) (storage blobs) queue fuel root).run (update nextState location updateResult) nextWorld := by
  rw [run]
  change (do
    let updateResult ← step (storage blobs) (fuel + 1) root location
    (queue (World := World)).complete location updateResult
    match updateResult with
    | .done outcome => result outcome
    | .runnable _ => run (α := α) (storage blobs) queue fuel root).run
      ⟨journal, location :: rest, none⟩ world = _
  rw [run_bind]
  cases updateResult with
  | done outcome =>
    simp only [executed]
    exact result_run outcome _ _
  | runnable locations =>
    simp only [executed]
    rfl

end LeanCloud.Proofs.ReplayModel
