import LeanCloud.Proofs.ExecutionTree
import LeanCloud.Proofs.Freshness

/-! Storage-bearing nodes in depth-first order. This order is proof data only;
it imposes no order on worker deliveries. Delays do not allocate locations. -/

namespace LeanCloud.Proofs
open Lean

mutual
  def ExecutionTree.nodes (tree : ExecutionTree) (location : Location) :
      List (Location × ExecutionTree) :=
    match tree with
    | .terminal _ => [(location, tree)]
    | .delay rest => rest.nodes location
    | .fork children _ next =>
      (location, tree) :: (childrenNodes children location 0 ++
        match next with
        | none => []
        | some rest => rest.nodes location.next)
  termination_by sizeOf tree

  def ExecutionTree.childrenNodes (trees : List ExecutionTree) (parent : Location) (offset : Nat) :
      List (Location × ExecutionTree) :=
    match trees with
    | [] => []
    | tree :: rest => tree.nodes (parent.child offset) ++ childrenNodes rest parent (offset + 1)
  termination_by sizeOf trees
end

private def Before (left right : Location) : Prop := left = right ∨ left.Earlier right

private theorem Before.trans {a b c : Location} (ab : Before a b) (bc : Before b c) : Before a c := by
  rcases ab with rfl | ab
  · exact bc
  rcases bc with rfl | bc
  · exact .inr ab
  · exact .inr (ab.trans bc)

private theorem earlier_before {a b c : Location} (ab : a.Earlier b) (bc : Before b c) : a.Earlier c := by
  rcases bc with rfl | bc
  · exact ab
  · exact ab.trans bc

mutual
  private theorem ExecutionTree.nodes_order (tree : ExecutionTree) (parent : Location) (branch command : Nat) :
      let start := parent.push (branch, command)
      let nodes := tree.nodes start
      nodes.Pairwise (fun a b => a.1.Earlier b.1) ∧
        ∀ node ∈ nodes, 0 < node.1.size ∧
          Before start node.1 ∧ node.1.Earlier (parent.child (branch + 1)) := by
    dsimp only
    cases tree with
    | terminal result =>
      simp only [nodes, List.pairwise_singleton, List.mem_singleton]
      refine ⟨trivial, ?_⟩
      rintro node rfl
      exact ⟨by simp, .inl rfl, Location.child_earlier_sibling _ _ _ _ (by omega)⟩
    | delay rest => simpa only [nodes] using rest.nodes_order parent branch command
    | fork children result next =>
      let start : Location := parent.push (branch, command)
      have nonempty : 0 < start.size := by simp [start]
      obtain ⟨childrenOrder, childrenBounds⟩ := childrenNodes_order children start 0
      have childBound : ∀ node ∈ childrenNodes children start 0,
          start.Earlier node.1 ∧ node.1.Earlier start.next := by
        intro node member
        obtain ⟨_, lower, upper⟩ := childrenBounds node member
        refine ⟨earlier_before (Location.earlier_child start 0) lower, ?_⟩
        apply upper.trans
        simpa only [Location.child, Array.push_eq_append, Nat.zero_add] using
          Location.descendants_earlier_next start #[(children.length, 0)] nonempty
      have upper : start.next.Earlier (parent.child (branch + 1)) := by
        simpa only [start, Location.next_push] using
          Location.child_earlier_sibling parent branch (command + 1) (branch + 1) (by omega)
      cases next with
      | none =>
        simp only [nodes, List.append_nil, List.pairwise_cons]
        refine ⟨⟨fun node member => (childBound node member).1, childrenOrder⟩, ?_⟩
        intro node member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨nonempty, .inl rfl, Location.child_earlier_sibling _ _ _ _ (by omega)⟩
        · exact ⟨(childrenBounds node member).1, .inr (childBound node member).1,
            (childBound node member).2.trans upper⟩
      | some rest =>
        obtain ⟨restOrder, restBounds⟩ := rest.nodes_order parent branch (command + 1)
        rw [← Location.next_push] at restOrder restBounds
        simp only [nodes, List.pairwise_cons, List.pairwise_append]
        refine ⟨⟨?_, childrenOrder, restOrder, ?_⟩, ?_⟩
        · intro node member
          rcases List.mem_append.mp member with member | member
          · exact (childBound node member).1
          · exact earlier_before (Location.earlier_next start nonempty) (restBounds node member).2.1
        · intro left leftMem right rightMem
          exact earlier_before (childBound left leftMem).2 (restBounds right rightMem).2.1
        · intro node member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨nonempty, .inl rfl, Location.child_earlier_sibling _ _ _ _ (by omega)⟩
          rcases List.mem_append.mp member with member | member
          · exact ⟨(childrenBounds node member).1, .inr (childBound node member).1,
              (childBound node member).2.trans upper⟩
          · obtain ⟨size, lower, upper⟩ := restBounds node member
            exact ⟨size, .inr (earlier_before (Location.earlier_next start nonempty) lower), upper⟩
  termination_by sizeOf tree

  private theorem ExecutionTree.childrenNodes_order (trees : List ExecutionTree) (parent : Location) (offset : Nat) :
      let nodes := childrenNodes trees parent offset
      nodes.Pairwise (fun a b => a.1.Earlier b.1) ∧
        ∀ node ∈ nodes, 0 < node.1.size ∧
          Before (parent.child offset) node.1 ∧ node.1.Earlier (parent.child (offset + trees.length)) := by
    dsimp only
    cases trees with
    | nil => simp [childrenNodes]
    | cons tree rest =>
      obtain ⟨firstOrder, firstBounds⟩ := tree.nodes_order parent offset 0
      obtain ⟨restOrder, restBounds⟩ := childrenNodes_order rest parent (offset + 1)
      have lower : Before (parent.child offset) (parent.child (offset + 1)) :=
        .inr (Location.child_earlier_sibling parent offset 0 (offset + 1) (by omega))
      have upper : Before (parent.child (offset + 1)) (parent.child (offset + (tree :: rest).length)) := by
        by_cases empty : rest.length = 0
        · left; simp [empty]
        · right; exact Location.child_earlier_sibling parent (offset + 1) 0 _ (by simp; omega)
      simp only [childrenNodes, List.pairwise_append]
      refine ⟨⟨firstOrder, restOrder, ?_⟩, ?_⟩
      · intro left leftMem right rightMem
        exact earlier_before (firstBounds left leftMem).2.2 (restBounds right rightMem).2.1
      · intro node member
        rcases List.mem_append.mp member with member | member
        · obtain ⟨size, first, last⟩ := firstBounds node member
          exact ⟨size, first, earlier_before last upper⟩
        · obtain ⟨size, first, last⟩ := restBounds node member
          exact ⟨size, lower.trans first, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using last⟩
  termination_by sizeOf trees
end

/-- The original location order is independent of worker scheduling. -/
theorem ExecutionTree.locations_order (tree : ExecutionTree) (location : Location)
    (nonempty : 0 < location.size) :
    ((tree.nodes location).map Prod.fst).Pairwise Location.Earlier := by
  obtain ⟨parent, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_size_pos nonempty
  rw [List.pairwise_map]
  exact (tree.nodes_order parent branch command).1

/-- Different storage-bearing tree positions have different runtime locations. -/
theorem ExecutionTree.locations_nodup (tree : ExecutionTree) (location : Location)
    (nonempty : 0 < location.size) : ((tree.nodes location).map Prod.fst).Nodup :=
  (tree.locations_order location nonempty).imp (fun earlier => earlier.ne)

theorem ExecutionTree.node_nonempty {tree : ExecutionTree} {location : Location}
    (nonempty : 0 < location.size) {node} (member : node ∈ tree.nodes location) : 0 < node.1.size := by
  obtain ⟨parent, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_size_pos nonempty
  exact ((tree.nodes_order parent branch command).2 node member).1

theorem ExecutionTree.node_at_or_after {tree : ExecutionTree} {location : Location}
    (nonempty : 0 < location.size) {node} (member : node ∈ tree.nodes location) :
    location = node.1 ∨ location.Earlier node.1 := by
  obtain ⟨parent, ⟨branch, command⟩, rfl⟩ := Array.exists_push_of_size_pos nonempty
  exact ((tree.nodes_order parent branch command).2 node member).2.1

mutual
  /-- Every descendant retains the branch index selected at its original fork. -/
  theorem ExecutionTree.node_path (tree : ExecutionTree) (parent : Location) (branch command : Nat)
      {target node} (member : (target, node) ∈ tree.nodes (parent.push (branch, command))) :
      parent.entersChild target = true ∧ target[parent.size]!.1 = branch := by
    cases tree with
    | terminal result =>
      simp only [nodes, List.mem_singleton] at member
      cases member
      simp [Location.entersChild]
    | delay rest =>
      rw [nodes] at member
      exact rest.node_path parent branch command member
    | fork children result next =>
      unfold nodes at member
      simp only [List.mem_cons, List.mem_append] at member
      rcases member with same | child | later
      · cases same; simp [Location.entersChild]
      · have enters := childrenNodes_path children (parent.push (branch, command)) 0 child
        refine ⟨Location.entersChild_trans (by simp [Location.entersChild]) enters, ?_⟩
        have retained := Location.entersChild_position enters parent.size (by simp)
        simpa using congrArg Prod.fst retained
      · cases next with
        | none => cases later
        | some rest =>
          rw [Location.next_push] at later
          exact rest.node_path parent branch (command + 1) later
  termination_by sizeOf tree

  theorem ExecutionTree.childrenNodes_path (trees : List ExecutionTree) (parent : Location) (offset : Nat)
      {target node} (member : (target, node) ∈ childrenNodes trees parent offset) :
      parent.entersChild target = true := by
    cases trees with
    | nil => simp [childrenNodes] at member
    | cons head tail =>
      rw [childrenNodes] at member
      rcases List.mem_append.mp member with first | later
      · exact (head.node_path parent offset 0 first).1
      · exact childrenNodes_path tail parent (offset + 1) later
  termination_by sizeOf trees
end

private theorem same_node {nodes : List (Location × ExecutionTree)}
    (distinct : (nodes.map Prod.fst).Nodup) {left right}
    (first : left ∈ nodes) (second : right ∈ nodes) (same : left.1 = right.1) : left = right := by
  induction nodes with
  | nil => cases first
  | cons head tail ih =>
    obtain ⟨absent, rest⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp first with rfl | firstTail <;>
      rcases List.mem_cons.mp second with rfl | secondTail
    · rfl
    · exact False.elim (absent (List.mem_map.mpr ⟨right, secondTail, same.symm⟩))
    · exact False.elim (absent (List.mem_map.mpr ⟨left, firstTail, same⟩))
    · exact ih rest firstTail secondTail

/-- A location identifies its entire command node, including its child outcomes. -/
theorem ExecutionTree.node_unique {tree : ExecutionTree} {location : Location}
    (nonempty : 0 < location.size) {left right}
    (first : left ∈ tree.nodes location) (second : right ∈ tree.nodes location)
    (same : left.1 = right.1) : left = right :=
  same_node (tree.locations_nodup location nonempty) first second same

end LeanCloud.Proofs
