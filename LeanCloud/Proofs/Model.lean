import LeanCloud.Db
import LeanCloud.BlobStorage

universe u

namespace LeanCloud.Proofs
open Lean

/-- The interpreter's records. There is no external user state in this model. -/
abbrev Journal := String → Option Json
namespace Journal
def empty : Journal := fun _ => none
def write (journal : Journal) (key : String) (value : Json) : Journal :=
  fun queriedKey => if queriedKey = key then some value else journal queriedKey
end Journal

/-- Unreachable for the pure fragment; supplied only to instantiate the runtime. -/
def noBlobs {m : Type → Type u} [Monad m] : BlobStorage σ m where
  putBlob _ := throw ⟨.unsupported, "Blob operations are outside the pure fragment"⟩
  readBlob _ := throw ⟨.unsupported, "Blob operations are outside the pure fragment"⟩
  resolveBlob _ := throw ⟨.unsupported, "Blob operations are outside the pure fragment"⟩

/-- Evaluate a bind in the model's state monad. -/
theorem run_bind_state {σ α β : Type}
    (action : ExceptT CloudError (StateT σ Id) α)
    (next : α → ExceptT CloudError (StateT σ Id) β) (state : σ) :
    (action >>= next).run state =
      let (outcome, state') := action.run state
      match outcome with
      | .ok value => (next value).run state'
      | .error error => (.error error, state') := by
  dsimp [ExceptT.run, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind]
  cases action state with
  | mk outcome state' => cases outcome <;> rfl

end LeanCloud.Proofs
