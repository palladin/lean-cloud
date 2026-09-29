import LeanCloud.Proofs.TreeActivation

/-! A branch's final command certifies its entire original subtree. The
activation path accounts for earlier joins and causal records account for all
their children. This supplies prerequisites for publishing the parent slot. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery

theorem ExecutionTree.Completed.terminal {result : Except CloudError Json} {current : Location} {journal : Journal}
    (recorded : CompletedAt journal current.key (encodeOutcome (inferInstance : Codec Json) result)) :
    (ExecutionTree.terminal result).Completed current journal := by
  intro location node member
  simp only [ExecutionTree.nodes, List.mem_singleton] at member
  cases member
  exact ⟨_, rfl, recorded⟩

theorem ExecutionTree.Completed.fork {children : List ExecutionTree} {result : Except CloudError Json}
    {next : Option ExecutionTree} {current : Location} {journal : Journal}
    (recorded : CompletedAt journal current.key (encodeOutcome (inferInstance : Codec Json) result))
    (finished : ∀ index : Fin children.length, children[index.val].Completed (current.child index.val) journal)
    (later : ∀ tree, next = some tree → tree.Completed current.next journal) :
    (ExecutionTree.fork children result next).Completed current journal := by
  intro location node member
  unfold ExecutionTree.nodes at member
  simp only [List.mem_cons, List.mem_append] at member
  rcases member with same | child | following
  · cases same; exact ⟨_, rfl, recorded⟩
  · obtain ⟨index, selected⟩ := (ExecutionTree.childrenNodes_mem children current 0 _).mp child
    exact finished index location node (by simpa using selected)
  · cases next with
    | none => cases following
    | some tree => exact later tree rfl location node following

/-- Finishing a terminal command or failed group finishes that command's
entire subtree. A successful group with a continuation cannot finish here. -/
theorem ExecutionTree.finish_completed {tree node : ExecutionTree} {root current : Location}
    {initial journal : Journal} (nonempty : 0 < root.size)
    (member : (current, node) ∈ tree.nodes root) (bounded : Extends journal (tree.journal root))
    (causal : tree.Causal root journal) (ready : node.FinishReady current initial)
    (recorded : CompletedAt journal current.key node.exit) : node.Completed current journal := by
  cases node with
  | terminal result => exact .terminal recorded
  | delay rest => cases ready
  | fork children result next =>
    cases next with
    | some _ => cases ready
    | none =>
      exact .fork recorded (causal.completed_children nonempty member bounded recorded)
        (fun _ same => by cases same)

/-- The final command either completes the branch being reconstructed or
completes one original child subtree. This certifies the parent-slot dependency;
it does not assume that the parent slot has already been written. -/
theorem TreeRoute.completed_branch {tree top : ExecutionTree} {root current target node}
    (route : TreeRoute tree current target node) {journal : Journal}
    (rootSize : 0 < root.size) (embedded : tree.nodes current ⊆ top.nodes root)
    (nonempty : 0 < current.size) (bounded : Extends journal (top.journal root))
    (causal : top.Causal root journal) (activated : route.Activated journal)
    (completed : node.Completed target journal) :
    (target.parent? = current.parent? ∧ tree.Completed current journal) ∨
      ∃ parent children result next, ∃ index : Fin children.length,
        (parent, ExecutionTree.fork children result next) ∈ tree.nodes current ∧
          target.parent? = some (parent, index.val) ∧
          children[index.val].Completed (parent.child index.val) journal := by
  induction route with
  | terminal | fork => exact .inl ⟨rfl, completed⟩
  | delay rest ih =>
    rcases ih (by simpa only [ExecutionTree.nodes] using embedded) nonempty activated completed with same |
      ⟨parent, children, result, next, index, member, linked, finished⟩
    · exact .inl ⟨same.1, by simpa only [ExecutionTree.Completed, ExecutionTree.nodes] using same.2⟩
    · exact .inr ⟨parent, children, result, next, index,
        by simpa only [ExecutionTree.nodes] using member, linked, finished⟩
  | @next children result tree current target node rest ih =>
    have member : (current, ExecutionTree.fork children result (some tree)) ∈ top.nodes root :=
      embedded (by simp [ExecutionTree.nodes])
    have included : tree.nodes current.next ⊆ top.nodes root :=
      fun _ h => embedded (by simp [ExecutionTree.nodes, h])
    rcases ih included (by simpa using nonempty) activated.2 completed with ⟨linked, finished⟩ |
      ⟨parent, descendants, childResult, later, index, member, linked, finished⟩
    · refine .inl ⟨linked.trans (Location.next_parent_eq current), ?_⟩
      apply ExecutionTree.Completed.fork activated.1
        (causal.completed_children rootSize member bounded activated.1)
      intro later same
      cases same
      exact finished
    · exact .inr ⟨parent, descendants, childResult, later, index,
        by simp [ExecutionTree.nodes, member], linked, finished⟩
  | @child children result next current target node index rest ih =>
    have subset := ExecutionTree.child_nodes_subset children result next current index
    rcases ih (subset.trans embedded) (by simp) activated.2 completed with ⟨linked, finished⟩ |
      ⟨parent, descendants, childResult, later, selected, member, linked, finished⟩
    · exact .inr ⟨current, children, result, next, index,
        by unfold ExecutionTree.nodes; exact List.mem_cons_self,
        linked.trans (Location.parent_child current nonempty index.val), finished⟩
    · exact .inr ⟨parent, descendants, childResult, later, selected, subset member, linked, finished⟩

/-- A non-root completion derives the actual parent slot's causal prerequisite
from reconstruction and the completed command, before publishing that slot. -/
theorem TreeRoute.parent_slot_requires {tree target node parent index journal}
    (route : TreeRoute tree Location.root target node)
    (linked : target.parent? = some (parent, index))
    (bounded : Extends journal (tree.journal Location.root)) (causal : tree.Causal Location.root journal)
    (activated : route.Activated journal) (completed : node.Completed target journal) :
    tree.Requires Location.root (childKey parent.key index) journal := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  rcases route.completed_branch rootSize (fun _ h => h) rootSize bounded causal activated completed with same |
    ⟨actual, children, result, next, selected, member, actualParent, finished⟩
  · have impossible := same.1
    rw [linked] at impossible
    simp [Location.root, Location.parent?] at impossible
  · rw [linked] at actualParent
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj actualParent)
    exact tree.requires_child rootSize member selected finished

theorem ExecutionTree.finish_requires_cache {tree node : ExecutionTree} {root current : Location}
    {journal : Journal} (nonempty : 0 < root.size) (member : (current, node) ∈ tree.nodes root)
    (bounded : Extends journal (tree.journal root)) (causal : tree.Causal root journal)
    (ready : node.FinishReady current journal) : tree.Requires root (resultKey current.key) journal := by
  cases node with
  | terminal result => exact tree.requires_terminal nonempty member journal
  | delay _ => cases ready
  | fork children result next =>
    cases next with
    | some _ => cases ready
    | none =>
      have recorded := tree.fork_completed_at nonempty member journal bounded ready
      exact tree.requires_cache nonempty member (causal.completed_children nonempty member bounded recorded)

end LeanCloud.Proofs
