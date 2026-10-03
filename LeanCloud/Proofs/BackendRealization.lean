import LeanCloud.Proofs.BackendFuelTrace

namespace LeanCloud.Backend.Proofs.Fuel
open Lean LeanEff LeanCloud.Proofs Execution Iteration

/-- The final iteration result becomes the actual public interpreter result,
with its cleared lease receipt; this is not merely a journal assertion. -/
theorem realizes_return [Codec α] {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enoughTraversal : sizeOf tree ≤ traversal)
    (trace : Iteration.Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (Iteration.program traversal source)))
    (limit : Nat) (budget : Nat → Nat) (enough : ∀ index, index < count → traversal + limit ≤ budget index)
    (worker : Nat) (attempt : Nat)
    (returned : (trace.states limit).workers[worker]? =
      some ⟨attempt, .finished (.ok (.ok (some tree.exit), ⟨(), none⟩))⟩) :
    ∃ remaining mapping target, Realizes (α := α) trace budget limit remaining mapping target ∧
      target.services = (trace.states limit).services ∧
      target.workers[worker]? = some ⟨attempt, .finished (.ok (Worker.expected tree, ⟨(), none⟩))⟩ := by
  obtain ⟨remaining, mapping, target, realized⟩ := finite_realization (α := α) whole supported comparable sameExit
    traversal enoughTraversal trace initialized limit budget enough
  refine ⟨remaining, mapping, target, realized, realized.related.services.symm, ?_⟩
  have finished := realized.related.workers worker _ returned
  change FuelStopped Worker.exhausted (.ok (.ok (some tree.exit), ⟨(), none⟩) : Outcome) ∨ _ at finished
  rcases finished with stopped | continued
  · obtain ⟨_, impossible⟩ := stopped
    cases impossible
  · have normalized : Program.ofEff (resume (α := α) (remaining worker) source
        (.ok (.ok (some tree.exit), ⟨(), none⟩))) = .pure (.ok (Worker.expected tree, ⟨(), none⟩)) := by
      simp only [resume]
      rw [Worker.result_eq]
      rfl
    rw [normalized] at continued
    cases continued with
    | pure held => exact held

end LeanCloud.Backend.Proofs.Fuel
