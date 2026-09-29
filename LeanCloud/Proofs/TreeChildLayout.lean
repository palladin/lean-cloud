import LeanCloud.Proofs.TreeSnapshot
import LeanCloud.Proofs.CompletionJournal

/-! Construct the local completion invariant from the pure program and an
actual suspended-parent read. Sibling slots are read from the current journal. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalLayout JournalAdapter ReplayRecovery

/-- The expected local journal is derived, including duplicate completion of
an already recorded child. Clearing a slot here only constructs proof data. -/
theorem Expansion.child_layout {m : Type → Type} {program : Cloud m Json} {tree : ExecutionTree}
    (expansion : Expansion program tree) {root current parent : Location} {node children result next slots outcome}
    (nonempty : 0 < root.size) (ownNode : (current, node) ∈ tree.nodes root)
    (ownResult : node.Admits (.completed outcome))
    (parentNode : (parent, .fork children result next) ∈ tree.nodes root)
    (index : Fin children.length) (linked : current.parent? = some (parent, index.val))
    (childResult : outcome = children[index.val].exit)
    (initial : Journal) (bounded : Extends initial (tree.journal root))
    (source : CompletionSource initial (tree.journal root) current.key outcome)
    (view : JournalDb.get raw parent.key initial = (some (toJson (Result.suspended slots)), initial)) :
    let baseline := slots.set! index.val none
    let expected := completionJournal initial current parent index.val outcome (baseline.set! index.val (some outcome))
    Between initial (tree.journal root) expected ∧
      ChildLayout initial expected current parent index.val outcome baseline := by
  dsimp only
  obtain ⟨uncached, descriptor, valid, physical⟩ := tree.suspended_snapshot nonempty parentNode initial bounded view
  let baseline := slots.set! index.val none
  let filled := baseline.set! index.val (some outcome)
  let expected := completionJournal initial current parent index.val outcome filled
  have inside : index.val < slots.size := by rw [valid.1]; exact index.isLt
  have prescribed : tree.journal root (resultKey current.key) = some (toJson outcome) := by
    apply tree.journal_contains root nonempty (resultKey current.key, toJson outcome)
    exact ExecutionTree.ownRecords_subset ownNode
      (ownResult.records current (by simp [JournalAdapter.records]))
  have child : tree.journal root (childKey parent.key index.val) = some (toJson outcome) := by
    simpa only [childResult] using (tree.fork_fields nonempty parentNode).2.2 index
  have correct : ExecutionTree.PartialSlots children filled := by
    simpa only [← childResult] using (valid.clear index).set index
  obtain ⟨subprogram, subexpansion⟩ := expansion.node parentNode
  have cache : ∀ value, Result.settle filled = .completed value →
      tree.journal root (resultKey parent.key) = some (toJson value) := by
    intro value settled
    have admitted := subexpansion.settle_admitted correct
    rw [settled] at admitted
    change value = encodeOutcome (inferInstance : Codec Json) result at admitted
    rw [admitted]
    exact (tree.fork_fields nonempty parentNode).2.1
  have interval := completionJournal_bounded bounded prescribed child cache
  have fields := completionJournal_fields initial current parent index.val outcome filled linked uncached
  change Between initial (tree.journal root) expected ∧ ChildLayout initial expected current parent index.val outcome baseline
  refine ⟨interval, ?_⟩
  refine ⟨fields.1, ?_, by simpa [baseline] using inside,
    Array.getElem!_set!_self _ _ _ inside, by simpa [baseline] using descriptor,
    ?_, fields.2.1, ?_, fields.2.2.1⟩
  · cases source with
    | completed recorded => exact .completed recorded
    | terminal missing =>
      apply CompletionSource.terminal
      exact (fields.2.2.2 (forkKey current.key)
        (result_ne_fork _ _).symm (fork_ne_child _ _ _) (result_ne_fork _ _).symm).trans
          (Extends.missing bounded _ missing)
  · exact (fields.2.2.2 (forkKey parent.key)
      (result_ne_fork _ _).symm (fork_ne_child _ _ _) (result_ne_fork _ _).symm).trans
        (by simpa [baseline] using descriptor)
  · intro i bound different
    have inSlots : i < slots.size := by simpa [baseline] using bound
    have sameSlot : baseline[i]! = slots[i]! := by
      simp [baseline, getElem!_pos, inSlots, Ne.symm different]
    have recorded : initial (childKey parent.key i) = baseline[i]!.map toJson := by
      rw [sameSlot]
      exact physical i inSlots
    refine ⟨recorded, ?_⟩
    exact (fields.2.2.2 (childKey parent.key i)
      (result_ne_child _ _ _).symm (fun same => different (child_key_injective same).2)
      (result_ne_child _ _ _).symm).trans recorded

end LeanCloud.Proofs
