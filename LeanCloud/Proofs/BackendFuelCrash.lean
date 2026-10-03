import LeanCloud.Proofs.BackendFuelReply

namespace LeanCloud.Backend.Proofs.Fuel
open Lean LeanEff LeanCloud.Proofs Execution Iteration

theorem Continues.orphan {owner crashed : Owner} {code : Program α} {state : Execution.State α}
    (continued : Continues owner code state) (different : crashed.worker ≠ owner.worker)
    (replacement : Execution.Worker α) :
    Continues owner code {state with
      workers := state.workers.setIfInBounds crashed.worker replacement
      calls := state.calls.map (Call.orphan crashed)} := by
  cases continued with
  | pure held => exact .pure (by simpa [Array.getElem?_setIfInBounds, different] using held)
  | request waiting =>
    refine .request ⟨by simpa [Array.getElem?_setIfInBounds, different] using waiting.1, ?_⟩
    have distinct : (owner == crashed) = false := by
      apply Bool.eq_false_iff.mpr
      intro equal
      exact different (congrArg Owner.worker ((owner_beq _ _).mp equal)).symm
    simp [Array.getElem?_map, waiting.2, Call.orphan, distinct]

theorem Related.crash [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after)
    (leftPrograms : Array (Backend.M Outcome)) (rightPrograms : Array (Backend.M (Answer α)))
    {index : Nat} {final : Execution.State Outcome}
    (executed : step leftPrograms (.crash index) before = .ok final) :
    ∃ target, Transition rightPrograms (.crash index) after target ∧
      Related remaining source mapping final target := by
  simp only [step] at executed
  split at executed <;> try contradiction
  rename_i worker held
  split at executed <;> try contradiction
  rename_i id status
  cases executed
  have corresponding := same.workers index worker held
  simp only [WorkerFollows, status] at corresponding
  let target : Execution.State (Answer α) := {after with
    workers := after.workers.setIfInBounds index ⟨worker.attempt, .stopped⟩
    calls := after.calls.map (Call.orphan ⟨index, worker.attempt⟩)}
  refine ⟨target, .crash ?_, ?_⟩
  · simp only [step, corresponding.2]; rfl
  constructor
  · exact same.services
  · simpa only [target, Array.size_setIfInBounds] using same.size
  · intro other current stored
    by_cases equal : index = other
    · subst other
      have inside := (Array.getElem?_eq_some_iff.mp held).choose
      simp only [Array.getElem?_setIfInBounds_self, inside, ↓reduceIte] at stored
      cases stored
      change target.workers[index]? = some ⟨worker.attempt, .stopped⟩
      simp [target, ← same.size, inside]
    · have old : before.workers[other]? = some current := by
        simpa only [Array.getElem?_setIfInBounds, equal, ↓reduceIte] using stored
      have previous := same.workers other current old
      simp only [WorkerFollows] at previous ⊢
      cases currentStatus : current.status with
      | stopped =>
        simp only [currentStatus] at previous
        simpa [target, Array.getElem?_setIfInBounds, equal] using previous
      | waiting call =>
        simp only [currentStatus] at previous
        exact ⟨by simpa using previous.1, by simpa [target, Array.getElem?_setIfInBounds, equal] using previous.2⟩
      | finished value =>
        simp only [currentStatus] at previous
        exact previous.imp_right (fun continued => Continues.orphan
          (crashed := ⟨index, worker.attempt⟩) continued equal ⟨worker.attempt, .stopped⟩)
  · intro id call stored
    simp only [Array.getElem?_map] at stored
    cases old : before.calls[id]? with
    | none => simp [old] at stored
    | some original =>
      simp only [old, Option.map_some] at stored
      cases stored
      obtain ⟨current, present, follows⟩ := same.calls id original old
      exact ⟨current.orphan ⟨index, worker.attempt⟩, by simp [target, Array.getElem?_map, present], follows.orphan _⟩
  · simpa only [Array.size_map] using same.injective

end LeanCloud.Backend.Proofs.Fuel
