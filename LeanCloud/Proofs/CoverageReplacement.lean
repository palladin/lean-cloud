import LeanCloud.Proofs.QueueCoverage

/-! Replacing one retained delivery by the locations emitted by the worker.
Completion requirements follow the branch's original parent and outcome. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery

/-- The root reports to the durable final cell; a child reports to its parent.
Successful sequential prefixes retain their branch's eventual outcome. -/
def BranchReported (journal : Journal) (rootDone : Prop) (tree : ExecutionTree) (current : Location) : Prop :=
  match current.parent? with
  | none => rootDone
  | some (parent, index) => ChildReported journal parent index tree.exit

private theorem Coverage.at_entry {journal pending} (tree : ExecutionTree) (current : Location) (rootDone : Prop)
    (provide : ∀ node, (current, node) ∈ tree.nodes current →
      Coverage journal pending node current (BranchReported journal rootDone node current)) :
    Coverage journal pending tree current (BranchReported journal rootDone tree current) := by
  cases tree with
  | terminal outcome => exact provide _ (by simp [ExecutionTree.nodes])
  | fork children result next => exact provide _ (by unfold ExecutionTree.nodes; exact List.mem_cons_self)
  | delay rest =>
    exact .delay (Coverage.at_entry rest current rootDone
      (fun node member => provide node (by simpa only [ExecutionTree.nodes] using member)))
termination_by sizeOf tree

/-- A local response can replace its delivery throughout the workflow. Only
coverage leaves that actually rely on this delivery need rebuilding; every
unrelated message remains available. -/
theorem Coverage.replace_work {journal before after tree current done selected rootDone}
    (covered : Coverage journal before tree current done) (nonempty : 0 < current.size)
    (reported : done = BranchReported journal rootDone tree current)
    (retains : ∀ location, before location → after location ∨ location = selected)
    (provide : ∀ location node, (location, node) ∈ tree.nodes current →
      WakePath journal selected location →
      Coverage journal after node location (BranchReported journal rootDone node location)) :
    Coverage journal after tree current done := by
  induction covered generalizing rootDone with
  | reported recorded => exact .reported recorded
  | queued available wake =>
    rcases retains _ available with retained | same
    · exact .queued retained wake
    · subst_vars
      apply Coverage.at_entry
      intro node member
      exact provide _ node member wake
  | delay rest ih =>
    apply Coverage.delay (ih nonempty reported ?_)
    intro location node member wake
    exact provide location node (by simpa only [ExecutionTree.nodes] using member) wake
  | @waiting children result next current done descriptor uncached missing represented ih =>
    refine .waiting descriptor uncached missing ?_
    intro index
    apply ih index (rootDone := rootDone) (by simp) ?_ ?_
    · simp [BranchReported, Location.parent_child current nonempty index.val]
    · intro location node member wake
      exact provide location node (ExecutionTree.child_nodes_subset children result next current index member) wake
  | @continued children result tree current done completed rest ih =>
    refine .continued completed (ih (rootDone := rootDone) (by simpa using nonempty) ?_ ?_)
    · simpa [BranchReported, Location.next_parent_eq, ExecutionTree.exit, ExecutionTree.outcome] using reported
    · intro location node member wake
      exact provide location node (by simp [ExecutionTree.nodes, member]) wake

/-- A live delivery with an incomplete parent cannot be supporting an ancestor
through the completed-parent shortcut. Its only wake target is itself. -/
theorem TreeRoute.wake_eq_of_open {tree current node journal target}
    (route : TreeRoute tree Location.root current node)
    (bounded : Extends journal (tree.journal Location.root)) (parentOpen : OpenParent journal current)
    (wake : WakePath journal current target) : current = target := by
  cases wake with
  | here => rfl
  | parent linked completed rest =>
    obtain ⟨slots, view⟩ := parentOpen _ _ linked
    obtain ⟨children, result, next, _, member, _⟩ := route.child_outcome linked
    have uncached := (tree.suspended_snapshot (by simp [Location.root]) member journal bounded view).1
    exact False.elim (completed.not_suspended uncached view)

namespace LeasePublication

/-- Removing one receipt leaves every other message slot intact, including
duplicate deliveries of the same location. -/
theorem Pending.remaining_or_selected {state receipt selected message}
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = selected)
    {location} (present : Pending state location) : Remaining state receipt location ∨ location = selected := by
  obtain ⟨other, member, value⟩ := present
  obtain ⟨index, inside, stored⟩ := Array.mem_iff_getElem.mp member
  have slot : state.transport.messages[index]? = some (some other) := by simp [inside, stored]
  by_cases same : receipt.message = index
  · have sameMessage := (LeaseQueue.current_iff.mp held).1
    rw [same, slot] at sameMessage
    have equal := Option.some.inj (Option.some.inj sameMessage)
    exact .inr (value.symm.trans ((congrArg LeaseQueueModel.Message.value equal).trans payload))
  · exact .inl ⟨index, other, same, slot, value⟩

/-- Instantiate structural replacement with the actual receipt and successor
array. The remaining obligation concerns the actual worker's branch behavior. -/
theorem Covered.replace {tree journal state receipt selected message locations}
    (covered : Covered tree journal state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = selected)
    (provide : ∀ location node, (location, node) ∈ tree.nodes Location.root →
      WakePath journal selected location →
      Coverage journal (fun next => Remaining state receipt next ∨ next ∈ locations) node location
        (BranchReported journal (state.completed = some tree.exit) node location)) :
    Replaced tree journal state receipt locations := by
  apply covered.replace_work (by simp [Location.root]) rfl _ provide
  intro location present
  rcases present.remaining_or_selected held payload with remaining | same
  · exact .inl (.inl remaining)
  · exact .inr same

/-- The actual parent response replaces an obsolete child message. The child
itself is discharged by the completed parent; any further ancestor it supported
is still reachable from the newly published parent message. -/
theorem Covered.replace_parent {tree journal state receipt selected message parent index outcome}
    (covered : Covered tree journal state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = selected)
    (linked : selected.parent? = some (parent, index)) (completed : CompletedAt journal parent.key outcome) :
    Replaced tree journal state receipt #[parent] := by
  apply covered.replace held payload
  intro location node _ wake
  cases wake with
  | here =>
    apply Coverage.reported
    simp only [BranchReported, linked]
    exact .inr ⟨outcome, completed⟩
  | parent actualLink _ rest =>
    rw [linked] at actualLink
    cases actualLink
    exact .queued (.inr (by simp)) rest

/-- Republishing the selected location preserves every responsibility of its
incoming message. This is the empty parallel group's initial response. -/
theorem Covered.replace_self {tree journal state receipt selected message}
    (covered : Covered tree journal state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = selected) :
    Replaced tree journal state receipt #[selected] := by
  apply covered.replace held payload
  intro location node _ wake
  exact .queued (.inr (by simp)) wake

/-- For a live delivery, a local coverage proof at its original program node
replaces the incoming message throughout the complete workflow. -/
theorem Covered.replace_live {tree journal state receipt selected message node locations}
    (covered : Covered tree journal state)
    (held : LeaseQueueModel.current receipt state.transport = some message) (payload : message.value = selected)
    (route : TreeRoute tree Location.root selected node)
    (bounded : Extends journal (tree.journal Location.root)) (parentOpen : OpenParent journal selected)
    (replacement : Coverage journal (fun location => Remaining state receipt location ∨ location ∈ locations)
      node selected (BranchReported journal (state.completed = some tree.exit) node selected)) :
    Replaced tree journal state receipt locations := by
  apply covered.replace held payload
  intro location other member wake
  have same := route.wake_eq_of_open bounded parentOpen wake
  subst location
  have sameNode := tree.node_unique (by simp [Location.root]) route.member member rfl
  cases sameNode
  exact replacement

end LeasePublication
end LeanCloud.Proofs
