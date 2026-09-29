import LeanCloud.Proofs.TreeRouting

/-! A reconstructed branch reports its result to its original parent slot.
The branch's final command may be later than its entry location. -/

namespace LeanCloud.Proofs
open Lean

def ExecutionTree.ChildCompletion (tree : ExecutionTree) (start current : Location) (outcome : Exit) : Prop :=
  ∃ parent children result next, ∃ index : Fin children.length,
    (parent, ExecutionTree.fork children result next) ∈ tree.nodes start ∧
      current.parent? = some (parent, index.val) ∧ outcome = children[index.val].exit

private theorem child_subset (children : List ExecutionTree) (result : Except CloudError Json)
    (next : Option ExecutionTree) (current : Location) (index : Fin children.length) :
    children[index.val].nodes (current.child index.val) ⊆ (ExecutionTree.fork children result next).nodes current := by
  intro entry member
  unfold ExecutionTree.nodes
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  exact (ExecutionTree.childrenNodes_mem children current 0 entry).mpr ⟨index, by simpa using member⟩

/-- Reconstructing within a branch preserves that branch's eventual outcome.
Entering a child switches to precisely that child's parent slot and outcome. -/
theorem TreeRoute.completion {tree current target node} (route : TreeRoute tree current target node)
    (nonempty : 0 < current.size) :
    (target.parent? = current.parent? ∧ node.exit = tree.exit) ∨
      tree.ChildCompletion current target node.exit := by
  induction route with
  | terminal => exact .inl ⟨rfl, rfl⟩
  | fork => exact .inl ⟨rfl, rfl⟩
  | delay rest ih =>
    rcases ih nonempty with same | ⟨parent, children, result, next, index, member, linked, outcome⟩
    · exact .inl same
    · exact .inr ⟨parent, children, result, next, index, by simpa only [ExecutionTree.nodes] using member, linked, outcome⟩
  | @next children result tree current target node rest ih =>
    rcases ih (by simpa using nonempty) with ⟨linked, outcome⟩ | ⟨parent, descendants, childResult, next, index, member, linked, outcome⟩
    · exact .inl ⟨linked.trans (Location.next_parent_eq current), outcome⟩
    · exact .inr ⟨parent, descendants, childResult, next, index,
        by simp [ExecutionTree.nodes, member], linked, outcome⟩
  | @child children result next current target node index rest ih =>
    rcases ih (by simp) with ⟨linked, outcome⟩ | ⟨parent, descendants, childResult, later, selected, member, linked, outcome⟩
    · exact .inr ⟨current, children, result, next, index,
        by unfold ExecutionTree.nodes; simp,
        linked.trans (Location.parent_child current nonempty index.val), outcome⟩
    · exact .inr ⟨parent, descendants, childResult, later, selected,
        child_subset children result next current index member, linked, outcome⟩

/-- A completion without a parent can only report the whole program's outcome. -/
theorem TreeRoute.root_outcome {tree target node} (route : TreeRoute tree Location.root target node)
    (root : target.parent? = none) : node.exit = tree.exit := by
  rcases route.completion (by simp [Location.root]) with same | ⟨_, _, _, _, _, _, linked, _⟩
  · exact same.2
  · rw [root] at linked
    cases linked

/-- A non-root completion identifies the original fork and array slot. -/
theorem TreeRoute.child_outcome {tree target node parent index}
    (route : TreeRoute tree Location.root target node)
    (linked : target.parent? = some (parent, index)) :
    ∃ children result next, ∃ inside : index < children.length,
      (parent, ExecutionTree.fork children result next) ∈ tree.nodes Location.root ∧
        node.exit = children[index].exit := by
  rcases route.completion (by simp [Location.root]) with same |
    ⟨actual, children, result, next, selected, member, actualParent, outcome⟩
  · have impossible := same.1
    rw [linked] at impossible
    simp [Location.root, Location.parent?] at impossible
  · rw [linked] at actualParent
    have equal := Option.some.inj actualParent
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    exact ⟨children, result, next, selected.isLt, member, outcome⟩

end LeanCloud.Proofs
