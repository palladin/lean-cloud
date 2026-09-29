import LeanCloud.Proofs.TreeChildLayout
import LeanCloud.Proofs.TreeCompletion
import LeanCloud.Proofs.ChildRecovery

/-! The actual child-completion recovery proof instantiated with a layout
derived from the original pure program and the current suspended-parent read. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery ReplayInterpreter.Internal

theorem Expansion.finish_child_from_tree {m : Type → Type} {program : Cloud m Json} {tree : ExecutionTree}
    (expansion : Expansion program tree) {root current parent : Location} {node children result next slots outcome}
    (nonempty : 0 < root.size) (ownNode : (current, node) ∈ tree.nodes root)
    (ownResult : node.Admits (.completed outcome))
    (parentNode : (parent, .fork children result next) ∈ tree.nodes root)
    (index : Fin children.length) (linked : current.parent? = some (parent, index.val))
    (childResult : outcome = children[index.val].exit)
    (initial : Journal) (bounded : Extends initial (tree.journal root))
    (source : CompletionSource initial (tree.journal root) current.key outcome)
    (view : JournalDb.get raw parent.key initial = (some (toJson (Result.suspended slots)), initial))
    (comparable : Comparable (tree.journal root)) (sameExit : (outcome == outcome) = true) :
    let updated := slots.set! index.val (some outcome)
    let expected := completionJournal initial current parent index.val outcome updated
    Between initial (tree.journal root) expected ∧
      Spec (Between initial expected) (finish db current outcome)
        (fun response journal => ChildFinished initial expected current outcome journal ∧
          JournalDb.get raw parent.key journal = (some (toJson (Result.settle updated)), journal) ∧
          response = completionResponse parent (Result.settle updated))
        (Between initial expected) := by
  obtain ⟨interval, layout⟩ := expansion.child_layout nonempty ownNode ownResult parentNode index linked
    childResult initial bounded source view
  have repeated : (slots.set! index.val none).set! index.val (some outcome) = slots.set! index.val (some outcome) := by
    simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
  rw [repeated] at interval layout
  refine ⟨interval, ?_⟩
  have safe := ReplayRecovery.finish_child_spec layout linked
    (fun key value recorded => comparable key value (interval.2 key value recorded)) sameExit
  simpa only [repeated] using safe

/-- Starting from this actual Db snapshot, a finishing child publishes only
its own result, its original parent slot, and a possible completed-parent cache. -/
theorem TreeRoute.finish_child {m : Type → Type} {program : Cloud m Json} {tree current node parent index slots}
    (expansion : Expansion program tree) (route : TreeRoute tree Location.root current node)
    (linked : current.parent? = some (parent, index))
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (view : JournalDb.get raw parent.key initial = (some (toJson (Result.suspended slots)), initial))
    (comparable : Comparable (tree.journal Location.root))
    (ready : node.FinishReady current initial) (sameExit : (node.exit == node.exit) = true) :
    let exit := node.exit
    let updated := slots.set! index (some exit)
    Spec (· = initial) (finish db current exit)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧
        CompletedAt journal current.key exit ∧
        JournalDb.get raw parent.key journal = (some (toJson (Result.settle updated)), journal) ∧
        response = completionResponse parent (Result.settle updated))
      (Between initial (tree.journal Location.root)) := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  obtain ⟨children, result, next, inside, parentNode, childResult⟩ := route.child_outcome linked
  obtain ⟨interval, safe⟩ := expansion.finish_child_from_tree rootSize route.member ready.admitted parentNode
    ⟨index, inside⟩ linked childResult initial bounded
    (tree.finish_source rootSize route.member bounded ready) view comparable sameExit
  apply safe.weaken
  · intro journal same
    subst journal
    exact ⟨Extends.refl _, interval.1⟩
  · intro response journal h
    exact ⟨⟨h.1.1.1, h.1.1.2.trans interval.2⟩, h.1.2, h.2⟩
  · intro journal h
    exact ⟨h.1, h.2.trans interval.2⟩

end LeanCloud.Proofs
