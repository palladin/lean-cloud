import LeanCloud.Proofs.TreeRecovery

/-! A structural path to a command in the pure execution tree. It contains no
worker execution or scheduling assumptions. -/

namespace LeanCloud.Proofs
open Lean

inductive TreeRoute : ExecutionTree → Location → Location → ExecutionTree → Type where
  | terminal (outcome) (current) : TreeRoute (.terminal outcome) current current (.terminal outcome)
  | fork (children result next current) :
      TreeRoute (.fork children result next) current current (.fork children result next)
  | delay {tree current target node} (rest : TreeRoute tree current target node) :
      TreeRoute (.delay tree) current target node
  | next {children result tree current target node} (rest : TreeRoute tree current.next target node) :
      TreeRoute (.fork children result (some tree)) current target node
  | child {children result next current target node} (index : Fin children.length)
      (rest : TreeRoute children[index.val] (current.child index.val) target node) :
      TreeRoute (.fork children result next) current target node

theorem ExecutionTree.childrenNodes_mem (trees : List ExecutionTree) (parent : Location) (offset : Nat)
    (entry : Location × ExecutionTree) :
    entry ∈ childrenNodes trees parent offset ↔
      ∃ index : Fin trees.length, entry ∈ trees[index.val].nodes (parent.child (offset + index.val)) := by
  induction trees generalizing offset with
  | nil => simp [childrenNodes]
  | cons head tail ih =>
    rw [childrenNodes, List.mem_append, ih]
    constructor
    · rintro (first | ⟨index, later⟩)
      · exact ⟨0, by simpa using first⟩
      · exact ⟨index.succ, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later⟩
    · rintro ⟨index, member⟩
      cases index using Fin.cases with
      | zero => exact .inl (by simpa using member)
      | succ i => exact .inr ⟨i, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using member⟩

theorem TreeRoute.member {tree current target node} (route : TreeRoute tree current target node) :
    (target, node) ∈ tree.nodes current := by
  induction route with
  | terminal => simp [ExecutionTree.nodes]
  | fork => unfold ExecutionTree.nodes; simp
  | delay _ ih => simpa only [ExecutionTree.nodes] using ih
  | next _ ih => simp [ExecutionTree.nodes, ih]
  | @child children result next current target node index rest ih =>
    unfold ExecutionTree.nodes
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact (ExecutionTree.childrenNodes_mem children current 0 _).mpr ⟨index, by simpa using ih⟩

/-- Delays have no storage address; routing passes through them to a command. -/
theorem TreeRoute.not_delay {tree current target node} (route : TreeRoute tree current target node)
    (rest : ExecutionTree) : node ≠ .delay rest := by
  induction route with
  | terminal => simp
  | fork => simp
  | delay _ ih | next _ ih | child _ _ ih => exact ih

theorem TreeRoute.nonempty {tree current target node} (route : TreeRoute tree current target node)
    (nonempty : 0 < current.size) : 0 < target.size :=
  ExecutionTree.node_nonempty nonempty route.member

theorem TreeRoute.next_ne {tree current target node} (route : TreeRoute tree current.next target node)
    (nonempty : 0 < current.size) : current ≠ target := by
  have first := Location.earlier_next current nonempty
  rcases ExecutionTree.node_at_or_after (by simpa using nonempty) route.member with same | later
  · exact (same ▸ first).ne
  · exact (first.trans later).ne

theorem TreeRoute.child_path {tree node : ExecutionTree} {current target : Location} {index : Nat}
    (route : TreeRoute tree (current.child index) target node) :
    current.entersChild target = true ∧ target[current.size]!.1 = index :=
  tree.node_path current index 0 route.member

/-- Locations obtained from the root program pass the public worker's guard. -/
theorem TreeRoute.root_guard {tree target node} (route : TreeRoute tree Location.root target node) :
    (target.isEmpty || target[0]!.1 != 0) = false := by
  have nonempty := route.nonempty (by simp [Location.root])
  have branch := (tree.node_path #[] 0 0 route.member).2
  have first : target[0]!.1 = 0 := by simpa using branch
  simp [Array.isEmpty, Nat.ne_of_gt nonempty, first]

/-- Prefix records needed to reconstruct this path. The target itself may be
missing, suspended, or completed. This is a predicate on concrete Db reads,
not an assumption that a worker step has returned successfully. -/
def TreeRoute.Ready {tree current target node} (route : TreeRoute tree current target node)
    (journal : Journal) : Prop :=
  match route with
  | .terminal .. | .fork .. => True
  | .delay rest => rest.Ready journal
  | @TreeRoute.next _ result _ current _ _ rest =>
    JournalDb.get JournalAdapter.raw current.key journal =
      (some (toJson (Result.completed (encodeOutcome (inferInstance : Codec Json) result))), journal) ∧
      rest.Ready journal
  | @TreeRoute.child children _ _ current _ _ _ rest =>
    ∃ slots : Array (Option Exit),
      JournalDb.get JournalAdapter.raw current.key journal = (some (toJson (Result.suspended slots)), journal) ∧
      slots.size = children.length ∧ rest.Ready journal

end LeanCloud.Proofs
