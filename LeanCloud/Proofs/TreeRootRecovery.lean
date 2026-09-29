import LeanCloud.Proofs.TreeCompletion
import LeanCloud.Proofs.TreeSnapshot

/-! Root completion connected to the pure program's outcome, rather than an
independently supplied expected result. -/

namespace LeanCloud.Proofs
open Lean JournalAdapter ReplayRecovery ReplayInterpreter.Internal

/-- An actual root completion reports the original program's result.
Its permitted Db records and its output both come from the execution tree. -/
theorem TreeRoute.finish_root {tree current node}
    (route : TreeRoute tree Location.root current node)
    (root : current.parent? = none) (comparable : Comparable (tree.journal Location.root))
    (sameExit : (node.exit == node.exit) = true) (initial : Journal)
    (bounded : Extends initial (tree.journal Location.root)) (ready : node.FinishReady current initial) :
    Spec (Between initial (tree.journal Location.root))
      (finish db current node.exit)
      (fun response journal => response = .done tree.exit ∧ Between initial (tree.journal Location.root) journal)
      (Between initial (tree.journal Location.root)) := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  have sameOutcome := route.root_outcome root
  have source := tree.finish_source rootSize route.member bounded ready
  have intended : tree.journal Location.root (JournalDb.resultKey current.key) = some (toJson node.exit) := by
    apply tree.journal_contains Location.root rootSize (JournalDb.resultKey current.key, toJson node.exit)
    exact ExecutionTree.ownRecords_subset route.member
      (ready.admitted.records current (by simp [records]))
  have saved := tree.save_admitted rootSize route.member ready.admitted comparable initial
  have returned : Spec (Between initial (tree.journal Location.root))
      (pure (StepResult.done node.exit))
      (fun response journal => response = .done tree.exit ∧ Between initial (tree.journal Location.root) journal)
      (Between initial (tree.journal Location.root)) :=
    (Spec.pure _ _).weaken (fun _ h => h)
      (fun _ _ h => ⟨h.1.trans (congrArg StepResult.done sameOutcome), h.2⟩) (fun _ h => h)
  rw [finish_eq, root]
  apply (recordResult_spec source intended sameExit (fun _ h => h) (fun _ h => h)
    (saved.weaken (fun _ h => h)
      (fun _ journal h => ⟨h.1, .cached (h.2 (JournalDb.resultKey current.key, toJson node.exit) (by simp [records]))⟩)
      (fun _ h => h))).bind
  exact fun _ => returned.weaken (fun _ h => h.1) (fun _ _ h => h) (fun _ h => h)

end LeanCloud.Proofs
