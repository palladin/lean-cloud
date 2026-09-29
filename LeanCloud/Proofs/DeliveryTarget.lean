import LeanCloud.Proofs.DeliveryCompletion
import LeanCloud.Proofs.WorkerCases

/-! Every live target action preserves workflow coverage and emits enough work
to replace the selected delivery. Reconstruction reads retain these guarantees. -/

namespace LeanCloud.Proofs
open Lean LeanEff CrashModel JournalAdapter ReplayRecovery ReplayInterpreter.Internal

/-- Activation and the existing causal invariant determine whether this is a
live or obsolete delivery. Both actual code paths supply replacement work. -/
theorem TreeRoute.activated_delivery {program : Cloud (M Journal) Json} {tree target node state receipt message}
    (expansion : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root target node)
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (causal : tree.Causal Location.root initial) (activated : route.Activated initial)
    (covered : LeasePublication.Covered tree initial state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = target)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit (M Journal)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel) :
    Spec (· = initial) (step db blobs fuel program target)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧
        LeasePublication.Covered tree journal state ∧ LeasePublication.CoversResponse tree journal state receipt response)
      (fun journal => Between initial (tree.journal Location.root) journal ∧ LeasePublication.Covered tree journal state) := by
  apply route.worker_cases expansion supported initial bounded causal activated blobs
    ⟨⟨Extends.refl _, bounded⟩, covered⟩ ?_ ?_ fuel enough
  · intro parentOpen
    obtain ⟨leaf, expanded⟩ := expansion.node route.member
    constructor
    · exact fun ready => route.finish_delivery expansion initial bounded covered held payload parentOpen comparable ready sameExit
    · intro children result next shape _
      subst node
      have available : LeasePublication.Pending state target :=
        ⟨message, Array.mem_of_getElem? (LeaseQueue.current_iff.mp held).1, payload⟩
      have initialized := expanded.initialize_fork_covered (by simp [Location.root]) route.member
        initial bounded covered available comparable
      apply Spec.bind (initialized.weaken
        (stopped' := fun journal => Between initial (tree.journal Location.root) journal ∧ LeasePublication.Covered tree journal state)
        (fun _ h => h) (fun _ _ h => h) (fun _ h => ⟨h.1, h.2.1⟩))
      intro _
      apply (Spec.pure _ _).weaken (fun _ h => h) _ (fun _ h => h)
      intro response journal ⟨same, progress, coveredNow, published, frame⟩
      subst response
      exact ⟨progress, coveredNow, LeasePublication.Covered.replace_initial expansion coveredNow held payload route progress.2
        (route.open_parent_command_frame bounded parentOpen frame) children.length rfl published⟩
    · intro children value next shape completed
      subst node
      exact Spec.return_at ⟨⟨Extends.refl _, bounded⟩, covered,
        covered.replace_join held payload route bounded parentOpen completed⟩
    · intro children result next shape slots view
      subst node
      exact Spec.return_at ⟨⟨Extends.refl _, bounded⟩, covered,
        covered.replace_missing expansion held payload route bounded parentOpen view children.length rfl⟩

  · intro parent index outcome linked view
    obtain ⟨children, result, next, _, member, _⟩ := route.child_outcome linked
    have completed := tree.fork_completed_at (by simp [Location.root]) member initial bounded view
    exact ⟨⟨Extends.refl _, bounded⟩, covered, covered.replace_parent held payload linked completed⟩

end LeanCloud.Proofs
