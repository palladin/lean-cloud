import LeanCloud.Proofs.TreeFinishCausality
import LeanCloud.Proofs.WorkerCases

/-! Safety of the actual replay action at its selected command. Fork creation,
missing-child publication, joins, and completion use the program's own tree. -/

namespace LeanCloud.Proofs
open Lean LeanEff CrashModel JournalAdapter ReplayRecovery ReplayInterpreter.Internal

/-- Actual worker safety with routing requirements derived from durable
activation. Both live and obsolete deliveries preserve causal dependencies
and emit only durably activated successors or the prescribed final outcome. -/
theorem TreeRoute.activated_step_spec {program : Cloud (CrashModel.M Journal) Json} {tree target node}
    (expansion : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root target node)
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (causal : tree.Causal Location.root initial) (activated : route.Activated initial)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (blobs : BlobStorage Unit (CrashModel.M Journal)) :
    ∀ fuel, route.prefixSteps + 1 ≤ fuel → Spec (· = initial)
      (ReplayInterpreter.Internal.step db blobs fuel program target)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧ tree.Causal Location.root journal ∧
        tree.EmitsActivated journal response)
      (fun journal => Between initial (tree.journal Location.root) journal ∧ tree.Causal Location.root journal) := by
  apply route.worker_cases expansion supported initial bounded causal activated blobs ⟨⟨Extends.refl _, bounded⟩, causal⟩
  · intro parentOpen
    obtain ⟨leaf, expanded⟩ := expansion.node route.member
    constructor
    · exact fun ready => route.finish_causal expansion initial bounded causal activated parentOpen ready comparable sameExit
    · intro children result next shape _
      subst node
      have initialized := expanded.initialize_fork_causal (by simp [Location.root]) route.member comparable initial
      apply Spec.bind (initialized.weaken (pre' := (· = initial))
        (by intro journal same; subst journal; exact ⟨⟨Extends.refl _, bounded⟩, causal⟩)
        (fun _ _ h => h) (fun _ h => h))
      intro _
      exact (Spec.pure _ _).weaken (fun _ h => h)
        (fun response journal ⟨same, kept, causalNow, published⟩ =>
          ⟨kept, causalNow, same ▸ route.emits_initial_activated (activated.grow kept.1) children.length rfl published⟩)
        (fun _ h => h)
    · intro children value next shape completed
      subst node
      exact Spec.return_at ⟨⟨Extends.refl _, bounded⟩, causal,
        ExecutionTree.EmitsActivated.singleton (activated.next completed)⟩
    · intro children result next shape slots view
      subst node
      have snapshot := tree.suspended_snapshot (by simp [Location.root]) route.member initial bounded view
      exact Spec.return_at ⟨⟨Extends.refl _, bounded⟩, causal,
        route.emits_missing_activated activated children.length rfl slots
          (by simpa only [snapshot.2.2.1.1] using snapshot.2.1)⟩

  · intro parent index _ linked _
    exact ⟨⟨Extends.refl _, bounded⟩, causal, ExecutionTree.EmitsActivated.singleton (activated.parent linked)⟩

end LeanCloud.Proofs
