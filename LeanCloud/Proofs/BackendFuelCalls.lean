import LeanCloud.Proofs.BackendFuelActivation

namespace LeanCloud.Backend.Proofs.Fuel
open Lean LeanEff LeanCloud.Proofs Execution Iteration

theorem Related.future_distinct [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after) (linked : Linked before)
    {index attempt returned id : Nat} {value : Outcome}
    (finished : before.workers[index]? = some ⟨attempt, .finished value⟩)
    {operation : Request β} {next : ArrsF Request β (Answer α)}
    (waiting : Waiting ⟨index, attempt⟩ returned operation next after)
    (inside : id < before.calls.size) : mapping id ≠ returned := by
  intro equal
  obtain ⟨call, stored, follows⟩ := same.calls id before.calls[id] (Array.getElem?_eq_getElem inside)
  rw [equal, waiting.2] at stored
  cases stored
  have caller : before.calls[id].caller = some ⟨index, attempt⟩ := follows.caller
  have held := linked id before.calls[id] (Array.getElem?_eq_getElem inside) ⟨index, attempt⟩ caller
  rw [finished] at held
  cases held

theorem Related.replace_call [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after) (linked : Linked before)
    (id : Nat) (inside : id < before.calls.size) (left : Call Outcome) (right : Call (Answer α))
    (follows : CallFollows remaining source left right) (services : Backend.State) :
    Related remaining source mapping
      {before with services, calls := before.calls.setIfInBounds id left}
      {after with services, calls := after.calls.setIfInBounds (mapping id) right} := by
  constructor
  · rfl
  · exact same.size
  · intro index worker held
    have previous := same.workers index worker held
    simp only [WorkerFollows] at previous ⊢
    cases status : worker.status with
    | stopped => simpa only [status] using previous
    | waiting call => simpa only [status, Array.size_setIfInBounds] using previous
    | finished returned =>
      simp only [status] at previous
      apply previous.imp_right
      intro continued
      generalize normalized : Program.ofEff (resume (α := α) (remaining index) source returned) = code at continued ⊢
      cases continued with
      | pure stored => exact .pure stored
      | request waiting =>
        have finished : before.workers[index]? = some ⟨worker.attempt, .finished returned⟩ := by
          rw [held]; congr; cases worker; simp_all
        have different := same.future_distinct linked finished waiting inside
        exact .request ⟨waiting.1, by simpa [Array.getElem?_setIfInBounds, different] using waiting.2⟩
  · intro other call held
    change (before.calls.setIfInBounds id left)[other]? = some call at held
    by_cases equal : id = other
    · subst other
      simp only [Array.getElem?_setIfInBounds_self, inside, ↓reduceIte] at held
      cases held
      exact ⟨right, by simp [same.mapped_inside inside], follows⟩
    · have old : before.calls[other]? = some call := by
        simpa [Array.getElem?_setIfInBounds, equal] using held
      have otherInside := (Array.getElem?_eq_some_iff.mp old).choose
      have different : mapping id ≠ mapping other := fun equ => equal (same.injective id other inside otherInside equ)
      obtain ⟨current, stored, related⟩ := same.calls other call old
      exact ⟨current, by simpa [Array.getElem?_setIfInBounds, different] using stored, related⟩
  · simpa only [Array.size_setIfInBounds] using same.injective

theorem Related.commit [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after) (linked : Linked before)
    {id : Nat} {owner : Owner} {operation : Request β} {next : Option (ArrsF Request β Outcome)}
    {value : β} {services : Backend.State}
    (issued : before.calls[id]? = some (.pending owner operation next))
    (lawful : Commits before.services operation value services)
    (programs : Array (Backend.M (Answer α))) :
    ∃ final, Transition programs (.commit (mapping id)) after final ∧
      Related remaining source mapping
        {before with services, calls := before.calls.setIfInBounds id (.committed owner operation value next)} final := by
  obtain ⟨call, stored, follows⟩ := same.calls id _ issued
  cases follows with
  | pending caller operation rest =>
    refine ⟨_, .commit stored (same.services ▸ lawful), ?_⟩
    exact same.replace_call linked id (Array.getElem?_eq_some_iff.mp issued).choose _ _
      (.committed _ _ _ rest) services

end LeanCloud.Backend.Proofs.Fuel
