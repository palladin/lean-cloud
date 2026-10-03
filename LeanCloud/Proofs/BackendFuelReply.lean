import LeanCloud.Proofs.BackendFuelCalls

namespace LeanCloud.Backend.Proofs.Fuel
open Lean LeanEff LeanCloud.Proofs Execution Iteration

theorem Related.reply [Codec α] {remaining source mapping before after}
    (same : Related (α := α) remaining source mapping before after) (linked : Linked before)
    (leftPrograms : Array (Backend.M Outcome)) (rightPrograms : Array (Backend.M (Answer α)))
    {id : Nat} {final : Execution.State Outcome}
    (executed : step leftPrograms (.reply id) before = .ok final) :
    ∃ target lastMap, Transition rightPrograms (.reply (mapping id)) after target ∧
      Related remaining source lastMap final target := by
  simp only [step] at executed
  split at executed <;> try contradiction
  rename_i β owner operation value next held
  obtain ⟨current, stored, follows⟩ := same.calls id _ held
  cases follows with
  | committed caller operation value continuation =>
    cases continuation with
    | orphan =>
      cases executed
      refine ⟨{after with calls := after.calls.setIfInBounds (mapping id) .retired}, mapping, .reply ?_, ?_⟩
      · simp only [step, stored]; rfl
      · simpa only [same.services] using same.replace_call linked id
          (Array.getElem?_eq_some_iff.mp held).choose .retired .retired .retired before.services
    | @live left right continuation =>
      simp only at executed
      split at executed <;> try contradiction
      rename_i owned
      cases executed
      have waiting := (owns_iff owner id before).mp owned
      have corresponding := same.workers owner.worker _ waiting
      change id < before.calls.size ∧
        after.workers[owner.worker]? = some ⟨owner.attempt, .waiting (mapping id)⟩ at corresponding
      have targetOwns := (owns_iff owner (mapping id) after).mpr corresponding.2
      have retired := same.replace_call linked id corresponding.1 .retired .retired .retired before.services
      simp only [same.services] at retired
      have rest : Follows (FuelStopped Worker.exhausted)
          (fun returned => Program.ofEff (resume (α := α) (remaining owner.worker) source returned))
          (Program.ofEff (ArrsF.apply left value)) (Program.ofEff (ArrsF.apply right value)) := by
        simpa only [Program.ofEff_apply] using continuation value
      obtain ⟨lastMap, activated⟩ := retired.activate owner (ArrsF.apply left value) (ArrsF.apply right value)
        (Array.getElem?_eq_some_iff.mp waiting).choose rest
      refine ⟨Execution.activate owner (ArrsF.apply right value)
        {after with calls := after.calls.setIfInBounds (mapping id) .retired}, lastMap, .reply ?_, ?_⟩
      · simp only [step, stored, targetOwns, ↓reduceIte]; rfl
      · simpa only [same.services] using activated

end LeanCloud.Backend.Proofs.Fuel
