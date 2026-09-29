import LeanCloud.Proofs.TreeNotificationCausality
import LeanCloud.Proofs.TreeSuccessors

/-! The actual completion sequence preserves both value agreement and causal
dependencies, including crashes between the child's result and its parent slot. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery ReplayInterpreter.Internal

theorem TreeRoute.finish_child_causal {m : Type → Type} {program : Cloud m Json}
    {tree current node parent index slots}
    (expansion : Expansion program tree) (route : TreeRoute tree Location.root current node)
    (linked : current.parent? = some (parent, index))
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (causal : tree.Causal Location.root initial) (activated : route.Activated initial)
    (view : JournalDb.get raw parent.key initial = (some (toJson (Result.suspended slots)), initial))
    (comparable : Comparable (tree.journal Location.root))
    (ready : node.FinishReady current initial) (sameExit : (node.exit == node.exit) = true) :
    Spec (· = initial) (finish db current node.exit)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧ tree.Causal Location.root journal ∧
        CompletedAt journal current.key node.exit ∧
        JournalDb.get raw parent.key journal =
          (some (toJson (Result.settle (slots.set! index (some node.exit)))), journal) ∧
        response = completionResponse parent (Result.settle (slots.set! index (some node.exit))))
      (fun journal => Between initial (tree.journal Location.root) journal ∧ tree.Causal Location.root journal) := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  obtain ⟨children, result, next, inside, parentNode, childResult⟩ := route.child_outcome linked
  obtain ⟨uncached, _, validSlots, _⟩ := tree.suspended_snapshot rootSize parentNode initial bounded view
  obtain ⟨expectedBound, layout⟩ := expansion.child_layout rootSize route.member ready.admitted parentNode
    ⟨index, inside⟩ linked childResult initial bounded
    (tree.finish_source rootSize route.member bounded ready) view
  let baseline := slots.set! index none
  let filled := baseline.set! index (some node.exit)
  let expected := completionJournal initial current parent index node.exit filled
  change Between initial (tree.journal Location.root) expected at expectedBound
  change ChildLayout initial expected current parent index node.exit baseline at layout
  have localComparable : Comparable expected :=
    fun key value recorded => comparable key value (expectedBound.2 key value recorded)
  have frame := (completionJournal_fields initial current parent index node.exit filled linked uncached).2.2.2
  let invariant := fun journal => Between initial expected journal ∧ tree.Causal Location.root journal
  let finished := fun journal => ChildFinished initial expected current node.exit journal ∧ tree.Causal Location.root journal
  let post := fun response journal => finished journal ∧
    JournalDb.get raw parent.key journal = (some (toJson (Result.settle filled)), journal) ∧
    response = completionResponse parent (Result.settle filled)
  have notify : Spec finished (notifyParent db parent index node.exit) post invariant := by
    intro start h
    obtain ⟨⟨progress, recorded⟩, causalNow⟩ := h
    have globalBound := progress.2.trans expectedBound.2
    have own := tree.finish_requires_cache rootSize route.member globalBound causalNow
      (ready.grow rootSize route.member progress.1 globalBound)
    have complete := tree.finish_completed rootSize route.member globalBound causalNow ready recorded
    have child := route.parent_slot_requires linked globalBound causalNow (activated.grow progress.1) complete
    have safe := layout.notify_causal rootSize parentNode (by simpa [baseline] using validSlots.1)
      frame progress causalNow own child recorded localComparable sameExit
    apply safe.weaken (fun _ h => h) _ _ start rfl
    · intro response journal h
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
    · intro journal h
      exact ⟨h.1.1, h.2⟩
  have ownAgrees : Agrees (records current.key (.completed node.exit)) expected := by
    intro entry member
    simp only [records, List.mem_singleton] at member
    subst entry
    exact ⟨layout.own, localComparable _ _ layout.own⟩
  have saved : Spec invariant (save db current (.completed node.exit)) (fun _ => finished) invariant := by
    apply (tree.save_causal_under Location.root expected initial current (.completed node.exit) ownAgrees (by
      intro entry member
      simp only [records, List.mem_singleton] at member
      subst entry
      exact tree.finish_requires_cache rootSize route.member bounded causal ready)).weaken
        (fun _ h => h) _ (fun _ h => h)
    intro _ journal h
    exact ⟨⟨h.1, .cached (h.2.2 (resultKey current.key, toJson node.exit) (by simp [records]))⟩, h.2.1⟩
  have complete : Spec invariant (finish db current node.exit) post invariant := by
    rw [finish_child_eq db current parent index node.exit linked]
    apply (recordResult_spec layout.source layout.own sameExit (fun _ h => h.1) (fun _ h => h)
      (saved.weaken (fun _ h => h) (fun _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩) (fun _ h => h))).bind
    exact fun _ => notify.weaken (fun _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩) (fun _ _ h => h) (fun _ h => h)
  have repeated : filled = slots.set! index (some node.exit) := by
    simp only [filled, baseline, Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]
  apply complete.weaken
  · intro journal same
    subst journal
    exact ⟨⟨Extends.refl _, expectedBound.1⟩, causal⟩
  · intro response journal h
    obtain ⟨⟨⟨progress, recorded⟩, causalNow⟩, observed, responseEq⟩ := h
    exact ⟨⟨progress.1, progress.2.trans expectedBound.2⟩, causalNow, recorded,
      by simpa only [repeated] using observed, by simpa only [repeated] using responseEq⟩
  · intro journal h
    exact ⟨⟨h.1.1, h.1.2.trans expectedBound.2⟩, h.2⟩

theorem TreeRoute.finish_root_causal {tree current node}
    (route : TreeRoute tree Location.root current node) (root : current.parent? = none)
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (causal : tree.Causal Location.root initial) (comparable : Comparable (tree.journal Location.root))
    (ready : node.FinishReady current initial) (sameExit : (node.exit == node.exit) = true) :
    Spec (fun journal => Between initial (tree.journal Location.root) journal ∧ tree.Causal Location.root journal)
      (finish db current node.exit)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧ tree.Causal Location.root journal ∧
        response = .done tree.exit)
      (fun journal => Between initial (tree.journal Location.root) journal ∧ tree.Causal Location.root journal) := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  let invariant := fun journal => Between initial (tree.journal Location.root) journal ∧ tree.Causal Location.root journal
  have source := tree.finish_source rootSize route.member bounded ready
  have intended : tree.journal Location.root (resultKey current.key) = some (toJson node.exit) := by
    apply tree.journal_contains Location.root rootSize (resultKey current.key, toJson node.exit)
    exact ExecutionTree.ownRecords_subset route.member (ready.admitted.records current (by simp [records]))
  have saved := tree.save_causal rootSize route.member ready.admitted comparable initial (by
    intro entry member
    simp only [records, List.mem_singleton] at member
    subst entry
    exact tree.finish_requires_cache rootSize route.member bounded causal ready)
  have returned : Spec invariant (pure (StepResult.done node.exit))
      (fun response journal => invariant journal ∧ response = .done tree.exit) invariant :=
    (Spec.pure invariant _).weaken (fun _ h => h)
      (fun _ _ h => ⟨h.2, h.1.trans (congrArg StepResult.done (route.root_outcome root))⟩) (fun _ h => h)
  have safe : Spec invariant (finish db current node.exit)
      (fun response journal => invariant journal ∧ response = .done tree.exit) invariant := by
    rw [finish_eq, root]
    apply (recordResult_spec source intended sameExit (fun _ h => h.1) (fun _ h => h)
      (saved.weaken (fun _ h => h)
        (fun _ journal h => ⟨⟨h.1, h.2.1⟩, .cached (h.2.2 (resultKey current.key, toJson node.exit) (by simp [records]))⟩)
        (fun _ h => h))).bind
    exact fun _ => returned.weaken (fun _ h => h.1) (fun _ _ h => h) (fun _ h => h)
  exact safe.weaken (fun _ h => h) (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ h => h)

/-- Completion preserves the whole causal invariant and emits a durably
activated parent or the pure program's outcome. -/
theorem TreeRoute.finish_causal {m : Type → Type} {program : Cloud m Json} {tree current node}
    (expansion : Expansion program tree) (route : TreeRoute tree Location.root current node)
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (causal : tree.Causal Location.root initial) (activated : route.Activated initial)
    (parentOpen : OpenParent initial current) (ready : node.FinishReady current initial)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true) :
    Spec (· = initial) (finish db current node.exit)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧ tree.Causal Location.root journal ∧
        tree.EmitsActivated journal response)
      (fun journal => Between initial (tree.journal Location.root) journal ∧ tree.Causal Location.root journal) := by
  cases linked : current.parent? with
  | none =>
    exact (route.finish_root_causal linked initial bounded causal comparable ready sameExit).weaken
      (by intro journal same; subst journal; exact ⟨⟨Extends.refl _, bounded⟩, causal⟩)
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2 ▸ rfl⟩) (fun _ h => h)
  | some pair =>
    obtain ⟨parent, index⟩ := pair
    obtain ⟨slots, view⟩ := parentOpen parent index linked
    apply (route.finish_child_causal expansion linked initial bounded causal activated view comparable ready sameExit).weaken
      (fun _ h => h) _ (fun _ h => h)
    intro response journal h
    refine ⟨h.1, h.2.1, ?_⟩
    rw [h.2.2.2.2]
    exact ExecutionTree.EmitsActivated.completion ((activated.parent linked).grow h.1.1) _

end LeanCloud.Proofs
