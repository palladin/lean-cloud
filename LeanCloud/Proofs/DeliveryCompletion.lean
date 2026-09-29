import LeanCloud.Proofs.CoverageResponses

/-! Completion and obsolete-delivery specifications include the actual queue
replacement obligation, as well as coverage retained at every crash boundary. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery ReplayInterpreter.Internal

/-- Initializing a command cannot change its enclosing group's suspended
read: their descriptors, result caches, and child slots have distinct keys. -/
theorem TreeRoute.open_parent_command_frame {tree current node before after}
    (route : TreeRoute tree Location.root current node)
    (bounded : Extends before (tree.journal Location.root)) (parentOpen : OpenParent before current)
    (frame : Frame [forkKey current.key, resultKey current.key] before after) :
    OpenParent after current := by
  intro parent index linked
  obtain ⟨slots, view⟩ := parentOpen parent index linked
  obtain ⟨children, result, next, _, member, _⟩ := route.child_outcome linked
  have differentResult : resultKey parent.key ≠ resultKey current.key :=
    fun same => Location.parent_key_ne linked (JournalLayout.result_key_injective same)
  have differentFork : forkKey parent.key ≠ forkKey current.key :=
    fun same => Location.parent_key_ne linked (JournalLayout.fork_key_injective same)
  refine ⟨slots, tree.suspended_frame (by simp [Location.root]) member bounded view ?_ ?_ ?_⟩
  · exact frame _ (by simp [differentResult, JournalLayout.result_ne_fork])
  · exact frame _ (by simp [differentFork, Ne.symm (JournalLayout.result_ne_fork current.key parent.key)])
  · intro child _
    exact frame _ (by simp [Ne.symm (JournalLayout.fork_ne_child current.key parent.key child),
      Ne.symm (JournalLayout.result_ne_child current.key parent.key child)])

theorem TreeRoute.finish_root_delivery {tree current node state receipt message}
    (route : TreeRoute tree Location.root current node) (root : current.parent? = none)
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (covered : LeasePublication.Covered tree initial state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = current)
    (comparable : Comparable (tree.journal Location.root))
    (ready : node.FinishReady current initial) (sameExit : (node.exit == node.exit) = true) :
    Spec (· = initial) (finish db current node.exit)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧
        LeasePublication.Covered tree journal state ∧ LeasePublication.CoversResponse tree journal state receipt response)
      (fun journal => Between initial (tree.journal Location.root) journal ∧ LeasePublication.Covered tree journal state) := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  have available : LeasePublication.Pending state current :=
    ⟨message, Array.mem_of_getElem? (LeaseQueue.current_iff.mp held).1, payload⟩
  have intended : tree.journal Location.root (resultKey current.key) = some (toJson node.exit) :=
    tree.journal_contains Location.root rootSize (resultKey current.key, toJson node.exit) (ExecutionTree.ownRecords_subset route.member
      (ready.admitted.records current (by simp [records])))
  have upper := extends_write bounded intended
  have retained (journal : Journal)
      (interval : Between initial (initial.write (resultKey current.key) (toJson node.exit)) journal) :
      Between initial (tree.journal Location.root) journal ∧ LeasePublication.Covered tree journal state := by
    refine ⟨⟨interval.1, interval.2.trans upper.2⟩, ?_⟩
    apply covered.grow_command rootSize route.member interval.1 available
    intro key outside
    have different : key ≠ resultKey current.key := by
      intro same
      exact outside (by simp [same])
    exact (show Between initial (initial.write (resultKey current.key) (toJson node.exit)) journal from interval).fixed key
      (Journal.read_write_other _ _ _ _ different)
  have source := tree.finish_source rootSize route.member bounded ready
  have saved := save_spec (initial.write (resultKey current.key) (toJson node.exit)) initial current
    (.completed node.exit) (by
      intro entry member
      simp only [records, List.mem_singleton] at member
      subst entry
      exact ⟨Journal.read_write _ _ _, comparable _ _ intended⟩)
  have recorded := recordResult_spec source intended sameExit (fun journal h => (retained journal h).1)
    (fun _ h => h) (saved.weaken (fun _ h => h)
      (fun _ journal h => ⟨⟨h.1, h.2.1⟩,
        .cached (h.2.2 (resultKey current.key, toJson node.exit) (by simp [records]))⟩) (fun _ h => h))
  rw [finish_eq, root]
  apply Spec.bind (recorded.weaken
    (pre' := (· = initial))
    (by intro journal same; subst journal; exact ⟨Extends.refl _, upper.1⟩)
    (fun _ _ h => h.1) retained)
  intro _ start valid
  exact ⟨Nat.le_refl _, .done node.exit, rfl, (retained _ valid).1,
    (retained _ valid).2, route.root_outcome root⟩

/-- Both root and child completion now discharge their actual response's
replacement requirement. Every interrupted completion retains global coverage. -/
theorem TreeRoute.finish_delivery {m : Type → Type} {program : Cloud m Json}
    {tree current node state receipt message}
    (expansion : Expansion program tree) (route : TreeRoute tree Location.root current node)
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (covered : LeasePublication.Covered tree initial state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = current)
    (parentOpen : OpenParent initial current) (comparable : Comparable (tree.journal Location.root))
    (ready : node.FinishReady current initial) (sameExit : (node.exit == node.exit) = true) :
    Spec (· = initial) (finish db current node.exit)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧
        LeasePublication.Covered tree journal state ∧ LeasePublication.CoversResponse tree journal state receipt response)
      (fun journal => Between initial (tree.journal Location.root) journal ∧ LeasePublication.Covered tree journal state) := by
  cases linked : current.parent? with
  | none => exact route.finish_root_delivery linked initial bounded covered held payload comparable ready sameExit
  | some pair =>
    obtain ⟨parent, index⟩ := pair
    obtain ⟨slots, view⟩ := parentOpen parent index linked
    exact route.finish_child_delivery expansion linked initial bounded covered held payload view comparable ready sameExit

end LeanCloud.Proofs
