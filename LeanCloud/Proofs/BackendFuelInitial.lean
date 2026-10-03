import LeanCloud.Proofs.BackendFuelIteration

namespace LeanCloud.Backend.Proofs.Fuel
open Lean LeanEff LeanCloud.Proofs Execution Iteration

private def activateAt (programs : Array (Backend.M α)) (state : Execution.State α) (index : Nat) :=
  match programs[index]? with | none => state | some code => Execution.activate ⟨index, 0⟩ code state

private theorem initial_fold (services : Backend.State) (programs : Array (Backend.M α)) :
    Execution.initial services programs = (List.range programs.size).foldl (activateAt programs)
      {services, workers := programs.map fun _ => ⟨0, .stopped⟩} := by
  unfold Execution.initial
  congr 1

theorem Related.initial [Codec α] (traversal : Nat) (source : Cloud Replay.M Json)
    (supported : PureProgram source) (count : Nat) (budget : Nat → Nat)
    (enough : ∀ index, index < count → traversal ≤ budget index + 1) :
    ∃ mapping, Related budget source mapping
      (Execution.initial Replay.initial (Array.replicate count (Iteration.program traversal source)))
      (Execution.initial Replay.initial ((Array.range count).map fun index => loop (α := α) (budget index + 1) source)) := by
  let left := Array.replicate count (Iteration.program traversal source)
  let right := (Array.range count).map fun index => loop (α := α) (budget index + 1) source
  let activateLeft := activateAt left
  let activateRight := activateAt right
  have fold (indices : List Nat) (bounded : ∀ index ∈ indices, index < count)
      (before : Execution.State Outcome) (after : Execution.State (Answer α))
      (size : before.workers.size = count) (mapping : Nat → Nat)
      (same : Related budget source mapping before after) :
      ∃ lastMap, Related budget source lastMap
        (indices.foldl activateLeft before) (indices.foldl activateRight after) := by
    induction indices generalizing before after mapping with
    | nil => exact ⟨mapping, same⟩
    | cons index rest ih =>
      have inside := bounded index (by simp)
      have sourceEntry : left[index]? = some (Iteration.program traversal source) := by simp [left, inside]
      have targetEntry : right[index]? = some (loop (α := α) (budget index + 1) source) := by simp [right, inside]
      obtain ⟨nextMap, related⟩ := same.activate ⟨index, 0⟩ _ _ (by simpa [size] using inside)
        (Follows.entry traversal (budget index) source supported (enough index inside))
      have nextSize : (Execution.activate ⟨index, 0⟩ (Iteration.program traversal source) before).workers.size = count := by
        generalize Iteration.program traversal source = code
        cases code <;> simpa only [Execution.activate, Array.size_setIfInBounds] using size
      simpa only [List.foldl_cons, activateLeft, activateRight, activateAt, sourceEntry, targetEntry] using
        ih (fun item member => bounded item (List.mem_cons_of_mem index member)) _ _ nextSize nextMap related
  have empty : Related (α := α) budget source id
      {services := Replay.initial, workers := left.map fun _ => ⟨0, .stopped⟩}
      {services := Replay.initial, workers := right.map fun _ => ⟨0, .stopped⟩} := by
    constructor
    · rfl
    · simp [left, right]
    · intro index worker held
      have inside : index < count := by simpa [left] using (Array.getElem?_eq_some_iff.mp held).choose
      have workerEq : worker = ⟨0, .stopped⟩ := by simpa [left, inside] using held.symm
      subst worker
      change (right.map fun _ => (⟨0, .stopped⟩ : Execution.Worker (Answer α)))[index]? = some ⟨0, .stopped⟩
      simp [right, inside]
    · intro index call held; simp at held
    · intro first last inside; simp at inside
  have result := fold (List.range count) (fun index member => List.mem_range.mp member) _ _
    (by simp [left]) id empty
  simpa only [initial_fold, activateLeft, activateRight, left, right, Array.size_replicate, Array.size_map, Array.size_range] using result

end LeanCloud.Backend.Proofs.Fuel
