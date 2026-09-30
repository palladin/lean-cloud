import LeanCloud.Proofs.TreeCoverage

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

/-- The queue has published a response: a final outcome is durable, or each
successor is available. Later fair delivery will instantiate `available`. -/
def ResponseAvailable (rootDone : Prop) (available : Location → Prop) : StepResult → Prop
  | .done _ => rootDone
  | .runnable locations => ∀ location ∈ locations, available location

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

end LeanCloud.Proofs
