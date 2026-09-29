import LeanCloud.Proofs.CoverageReplacement
import LeanCloud.Proofs.CoveragePublication

/-! Structural coverage of the actual worker's runnable responses. These
discharge replacement obligations from durable records and program locations. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery

theorem Expansion.suspended_missing {m : Type → Type} {program : Cloud m Json}
    {tree root location children result next slots journal}
    (expansion : Expansion program tree) (nonempty : 0 < root.size)
    (member : (location, ExecutionTree.fork children result next) ∈ tree.nodes root)
    (bounded : Extends journal (tree.journal root))
    (view : JournalDb.get raw location.key journal = (some (toJson (Result.suspended slots)), journal)) :
    ∃ index : Fin children.length, journal (childKey location.key index.val) = none := by
  obtain ⟨uncached, descriptor, valid, _⟩ := tree.suspended_snapshot nonempty member journal bounded view
  rcases expansion.fork_coverage_cases nonempty member journal bounded (by simpa only [valid.1] using descriptor) with
    waiting | completed
  · exact waiting.2
  · exact False.elim (completed.not_suspended uncached view)

namespace LeasePublication

/-- A suspended fork is covered by exactly its missing children; recorded
children are already discharged by their durable parent slots. -/
theorem Covered.replace_waiting {m : Type → Type} {program : Cloud m Json}
    {tree journal state receipt current message children result next slots locations}
    (expansion : Expansion program tree) (covered : Covered tree journal state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = current)
    (route : TreeRoute tree Location.root current (.fork children result next))
    (bounded : Extends journal (tree.journal Location.root)) (parentOpen : OpenParent journal current)
    (view : JournalDb.get raw current.key journal = (some (toJson (Result.suspended slots)), journal))
    (published : ∀ index : Fin children.length, journal (childKey current.key index.val) = none →
      current.child index.val ∈ locations) :
    Replaced tree journal state receipt locations := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  obtain ⟨uncached, descriptor, valid, _⟩ := tree.suspended_snapshot rootSize route.member journal bounded view
  apply covered.replace_live held payload route bounded parentOpen
  refine .waiting (by simpa only [valid.1] using descriptor) uncached
    (expansion.suspended_missing rootSize route.member bounded view) ?_
  intro index
  cases stored : journal (childKey current.key index.val) with
  | none => exact .queued (.inr (published index stored)) (.here _)
  | some value =>
    have same := (bounded _ _ stored).symm.trans ((tree.fork_fields rootSize route.member).2.2 index)
    cases same
    exact .reported (.inl stored)

/-- The filter used by the actual suspended-fork handler publishes every
missing physical child slot, preserving the child's original index. -/
theorem Covered.replace_missing {m : Type → Type} {program : Cloud m Json}
    {tree journal state receipt current message children result next slots}
    (expansion : Expansion program tree) (covered : Covered tree journal state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = current)
    (route : TreeRoute tree Location.root current (.fork children result next))
    (bounded : Extends journal (tree.journal Location.root)) (parentOpen : OpenParent journal current)
    (view : JournalDb.get raw current.key journal = (some (toJson (Result.suspended slots)), journal))
    (count : Nat) (size : children.length = count) :
    Replaced tree journal state receipt ((Array.ofFn fun index : Fin count => index.val).filterMap fun index =>
      if slots[index]!.isNone then some (current.child index) else none) := by
  apply covered.replace_waiting expansion held payload route bounded parentOpen view
  intro index absent
  have snapshot := tree.suspended_snapshot (by simp [Location.root]) route.member journal bounded view
  have physical := snapshot.2.2.2 index.val (by rw [snapshot.2.2.1.1]; exact index.isLt)
  have empty : slots[index.val]! = none := by
    cases slot : slots[index.val]! with
    | none => rfl
    | some value => simp [slot, absent] at physical
  apply Array.mem_filterMap.mpr
  refine ⟨index.val, Array.mem_ofFn.mpr ⟨⟨index.val, by omega⟩, rfl⟩, ?_⟩
  simp [empty]

/-- Advancing a completed successful group transfers responsibility to its
continuation, whose branch and final outcome remain the same. -/
theorem Covered.replace_join {tree journal state receipt current message children result next}
    (covered : Covered tree journal state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = current)
    (route : TreeRoute tree Location.root current (.fork children result (some next)))
    (bounded : Extends journal (tree.journal Location.root)) (parentOpen : OpenParent journal current)
    (completed : CompletedAt journal current.key (encodeOutcome (inferInstance : Codec Json) result)) :
    Replaced tree journal state receipt #[current.next] := by
  apply covered.replace_live held payload route bounded parentOpen
  exact .continued completed (.queued (.inr (by simp)) (.here _))

/-- Initial publication covers every child. If all child results were already
durable, any published child can instead wake the completed group. -/
theorem Covered.replace_initial {m : Type → Type} {program : Cloud m Json}
    {tree journal state receipt current message children result next}
    (expansion : Expansion program tree) (covered : Covered tree journal state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = current)
    (route : TreeRoute tree Location.root current (.fork children result next))
    (bounded : Extends journal (tree.journal Location.root)) (parentOpen : OpenParent journal current)
    (count : Nat) (size : children.length = count)
    (published : Published (records current.key (Result.settle (Array.replicate count none))) journal) :
    Replaced tree journal state receipt
      (if count == 0 then #[current] else Array.ofFn fun index : Fin count => current.child index.val) := by
  by_cases empty : count = 0
  · simp only [empty, beq_self_eq_true, ↓reduceIte]
    exact covered.replace_self held payload
  · simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ↓reduceIte]
    have hasMissing : none ∈ (Array.replicate count none : Array (Option Exit)) := by simp [empty]
    rw [Result.settle_missing _ hasMissing] at published
    have descriptor : journal (forkKey current.key) = some (toJson children.length) := by
      simpa only [Array.size_replicate, size] using (published_fork published).1
    apply covered.replace_live held payload route bounded parentOpen
    rcases expansion.fork_coverage_cases (by simp [Location.root]) route.member journal bounded descriptor with
      ⟨uncached, missing⟩ | completed
    · refine .waiting descriptor uncached missing ?_
      intro index
      exact .queued (.inr (Array.mem_ofFn.mpr ⟨⟨index.val, by omega⟩, rfl⟩)) (.here _)
    · have positive : 0 < count := by omega
      exact .queued (.inr (Array.mem_ofFn.mpr ⟨⟨0, positive⟩, rfl⟩))
        (.parent (Location.parent_child current (route.nonempty (by simp [Location.root])) 0) completed (.here current))

/-- A child with a recorded parent slot can relinquish its delivery when the
parent is still suspended. No successor is required from that child. -/
theorem Covered.replace_finished_child {tree journal state receipt current message node parent index slots}
    (covered : Covered tree journal state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = current)
    (route : TreeRoute tree Location.root current node)
    (bounded : Extends journal (tree.journal Location.root))
    (linked : current.parent? = some (parent, index))
    (view : JournalDb.get raw parent.key journal = (some (toJson (Result.suspended slots)), journal))
    (reported : ChildReported journal parent index node.exit) :
    Replaced tree journal state receipt #[] := by
  have parentOpen : OpenParent journal current := by
    intro other child actual
    rw [linked] at actual
    cases actual
    exact ⟨slots, view⟩
  apply covered.replace_live held payload route bounded parentOpen
  apply Coverage.reported
  simpa only [BranchReported, linked] using reported

end LeasePublication

/-- The actual child's response discharges the queue's replacement obligation.
If the group is still partial the recorded slot suffices; if it has completed,
the returned parent message carries the remaining responsibility. -/
theorem TreeRoute.finish_child_delivery {m : Type → Type} {program : Cloud m Json}
    {tree current node parent index slots state receipt message}
    (expansion : Expansion program tree) (route : TreeRoute tree Location.root current node)
    (linked : current.parent? = some (parent, index))
    (initial : Journal) (bounded : Extends initial (tree.journal Location.root))
    (covered : LeasePublication.Covered tree initial state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = current)
    (view : JournalDb.get raw parent.key initial = (some (toJson (Result.suspended slots)), initial))
    (comparable : Comparable (tree.journal Location.root))
    (ready : node.FinishReady current initial) (sameExit : (node.exit == node.exit) = true) :
    Spec (· = initial) (ReplayInterpreter.Internal.finish db current node.exit)
      (fun response journal => Between initial (tree.journal Location.root) journal ∧
        LeasePublication.Covered tree journal state ∧ LeasePublication.CoversResponse tree journal state receipt response)
      (fun journal => Between initial (tree.journal Location.root) journal ∧ LeasePublication.Covered tree journal state) := by
  have available : LeasePublication.Pending state current :=
    ⟨message, Array.mem_of_getElem? (LeaseQueue.current_iff.mp held).1, payload⟩
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  obtain ⟨children, result, next, inside, parentNode, _⟩ := route.child_outcome linked
  have before := tree.suspended_snapshot rootSize parentNode initial bounded view
  have slotBound : index < slots.size := by rw [before.2.2.1.1]; exact inside
  apply (route.finish_child_covered expansion linked initial bounded covered available view comparable ready sameExit).weaken
    (fun _ h => h) _ (fun _ h => h)
  intro response journal h
  obtain ⟨progress, coveredNow, _, parentView, rfl⟩ := h
  refine ⟨progress, coveredNow, ?_⟩
  cases settled : Result.settle (slots.set! index (some node.exit)) with
  | completed outcome =>
    rw [settled] at parentView
    exact LeasePublication.Covered.replace_parent coveredNow held payload linked
      (tree.fork_completed_at rootSize parentNode journal progress.2 parentView)
  | suspended remaining =>
    rw [settled] at parentView
    have after := tree.suspended_snapshot rootSize parentNode journal progress.2 parentView
    have physical := after.2.2.2 index (by rw [after.2.2.1.1]; exact inside)
    have same := Result.settle_suspended settled
    rw [← same, Array.getElem!_set!_self _ _ _ slotBound] at physical
    exact LeasePublication.Covered.replace_finished_child coveredNow held payload route progress.2 linked parentView (.inl physical)

end LeanCloud.Proofs
