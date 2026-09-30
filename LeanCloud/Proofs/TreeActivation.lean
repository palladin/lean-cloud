import LeanCloud.Proofs.TreeCausality
import LeanCloud.Proofs.TreeCompletion
import LeanCloud.Proofs.TreeSnapshot

/-! Durable prerequisites for an issued location. Unlike a suspended read,
activation survives later completions. Causality then shows that the delivery
is still replayable or is obsolete at its immediate parent. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery

def TreeRoute.Activated {tree current target node} (route : TreeRoute tree current target node)
    (journal : Journal) : Prop :=
  match route with
  | .terminal .. | .fork .. => True
  | .delay rest => rest.Activated journal
  | @TreeRoute.next _ result _ current _ _ rest =>
    CompletedAt journal current.key (encodeOutcome (inferInstance : Codec Json) result) ∧ rest.Activated journal
  | @TreeRoute.child children result _ current _ _ _ rest =>
    (journal (forkKey current.key) = some (toJson children.length) ∨
      CompletedAt journal current.key (encodeOutcome (inferInstance : Codec Json) result)) ∧ rest.Activated journal

theorem TreeRoute.Activated.grow {tree current target node} {route : TreeRoute tree current target node}
    {before after : Journal} (activated : route.Activated before) (growth : Extends before after) :
    route.Activated after := by
  induction route with
  | terminal | fork => trivial
  | delay rest ih => exact ih activated
  | next rest ih => exact ⟨activated.1.grow growth, ih activated.2⟩
  | child index rest ih =>
    exact ⟨activated.1.elim (fun descriptor => .inl (growth _ _ descriptor))
      (fun completed => .inr (completed.grow growth)), ih activated.2⟩

/-- The actual worker handles this delivery by republishing its completed
immediate parent, without replaying the branch. -/
def Obsolete (journal : Journal) (location : Location) : Prop :=
  ∃ parent index outcome, location.parent? = some (parent, index) ∧
    JournalDb.get raw parent.key journal = (some (toJson (Result.completed outcome)), journal)

theorem ExecutionTree.child_nodes_subset (children : List ExecutionTree) (result : Except CloudError Json)
    (next : Option ExecutionTree) (current : Location) (index : Fin children.length) :
    children[index.val].nodes (current.child index.val) ⊆ (ExecutionTree.fork children result next).nodes current := by
  intro entry member
  unfold ExecutionTree.nodes
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  exact (ExecutionTree.childrenNodes_mem children current 0 entry).mpr ⟨index, by simpa using member⟩

private theorem TreeRoute.completed_obsolete {top tree : ExecutionTree} {root current target node}
    (route : TreeRoute tree current target node) (nonempty : 0 < current.size)
    (rootSize : 0 < root.size) (embedded : tree.nodes current ⊆ top.nodes root)
    {journal : Journal} (bounded : Extends journal (top.journal root))
    (closed : tree.Completed current journal) (obsolete : Obsolete journal current) : Obsolete journal target := by
  rcases route.completion nonempty with ⟨linked, _⟩ | ⟨parent, children, result, next, index, member, linked, _⟩
  · obtain ⟨parent, index, outcome, original, view⟩ := obsolete
    exact ⟨parent, index, outcome, linked.trans original, view⟩
  · obtain ⟨outcome, admitted, recorded⟩ := closed parent (.fork children result next) member
    exact ⟨parent, index.val, outcome, linked,
      top.completed_view rootSize (embedded member) bounded admitted recorded⟩

private theorem Expansion.activated_fork_view {m : Type → Type} {program : Cloud m Json} {top : ExecutionTree}
    (expansion : Expansion program top) {root current children result next journal}
    (rootSize : 0 < root.size) (member : (current, .fork children result next) ∈ top.nodes root)
    (bounded : Extends journal (top.journal root))
    (opened : journal (forkKey current.key) = some (toJson children.length) ∨
      CompletedAt journal current.key (encodeOutcome (inferInstance : Codec Json) result)) :
    ∃ record, JournalDb.get raw current.key journal = (some (toJson record), journal) ∧
      (ExecutionTree.fork children result next).Admits record := by
  rcases opened with descriptor | completed
  · cases cached : journal (resultKey current.key) with
    | some value =>
      have same := (bounded _ _ cached).symm.trans (top.fork_fields rootSize member).2.1
      cases same
      exact ⟨_, get_completed _ _ _ cached, rfl⟩
    | none =>
      let slots := ExecutionTree.observedSlots children journal current
      obtain ⟨valid, physical⟩ := top.observedSlots_spec rootSize member journal bounded
      obtain ⟨leaf, expanded⟩ := expansion.node member
      refine ⟨Result.settle slots, ?_, expanded.settle_admitted valid⟩
      apply get_fork journal current.key slots cached
      · simpa [slots, ExecutionTree.observedSlots] using descriptor
      · intro index inside
        exact physical index (by simpa [slots, ExecutionTree.observedSlots] using inside)
  · exact ⟨_, completed.view bounded (top.fork_fields rootSize member).2.1, rfl⟩

/-- Activation and causal completion records derive the worker's ready-path
condition, or justify its existing obsolete-delivery shortcut. -/
theorem TreeRoute.activated_cases {m : Type → Type} {program : Cloud m Json} {top tree : ExecutionTree}
    (expansion : Expansion program top) {root current target node}
    (route : TreeRoute tree current target node) {journal : Journal}
    (rootSize : 0 < root.size) (embedded : tree.nodes current ⊆ top.nodes root)
    (nonempty : 0 < current.size) (bounded : Extends journal (top.journal root))
    (causal : top.Causal root journal) (activated : route.Activated journal) :
    route.Ready journal ∨ Obsolete journal target := by
  induction route with
  | terminal | fork => exact .inl trivial
  | delay rest ih => exact ih (by simpa only [ExecutionTree.nodes] using embedded) nonempty activated
  | @next children result tree current target node rest ih =>
    have member : (current, ExecutionTree.fork children result (some tree)) ∈ top.nodes root :=
      embedded (by simp [ExecutionTree.nodes])
    have view := activated.1.view bounded (top.fork_fields rootSize member).2.1
    have included : tree.nodes current.next ⊆ top.nodes root :=
      fun _ h => embedded (by simp [ExecutionTree.nodes, h])
    rcases ih included (by simpa using nonempty) activated.2 with ready | obsolete
    · exact .inl ⟨view, ready⟩
    · exact .inr obsolete
  | @child children result next current target node index rest ih =>
    have member : (current, ExecutionTree.fork children result next) ∈ top.nodes root :=
      embedded (by unfold ExecutionTree.nodes; exact List.mem_cons_self)
    have included := (ExecutionTree.child_nodes_subset children result next current index).trans embedded
    obtain ⟨record, view, admitted⟩ := expansion.activated_fork_view rootSize member bounded activated.1
    cases record with
    | suspended slots =>
      rcases ih included (by simp) activated.2 with ready | obsolete
      · exact .inl ⟨slots, view, admitted.1, ready⟩
      · exact .inr obsolete
    | completed outcome =>
      have recorded := top.fork_completed_at rootSize member journal bounded view
      have closed := causal.completed_children rootSize member bounded recorded index
      exact .inr (rest.completed_obsolete (by simp) rootSize included bounded closed
        ⟨current, index.val, outcome, Location.parent_child current nonempty index.val, view⟩)

/-- A ready reconstruction path supplies its last open parent as well. -/
theorem TreeRoute.Ready.open_parent {tree current target node} {route : TreeRoute tree current target node}
    {journal : Journal} (ready : route.Ready journal) (nonempty : 0 < current.size)
    (opened : OpenParent journal current) : OpenParent journal target := by
  induction route with
  | terminal | fork => exact opened
  | delay rest ih => exact ih ready nonempty opened
  | @next children result tree current target node rest ih =>
    apply ih ready.2 (by simpa using nonempty)
    intro parent index linked
    exact opened parent index ((Location.next_parent_eq current).symm.trans linked)
  | @child children result next current target node index rest ih =>
    obtain ⟨slots, view, _, remaining⟩ := ready
    apply ih remaining (by simp)
    intro parent child linked
    rw [Location.parent_child current nonempty index.val] at linked
    cases linked
    exact ⟨slots, view⟩

/-- A delivered location's durable activation is enough to derive all routing
preconditions, provided the global causal and value invariants hold. -/
theorem TreeRoute.delivery_ready {m : Type → Type} {program : Cloud m Json} {tree target node}
    (expansion : Expansion program tree) (route : TreeRoute tree Location.root target node)
    {journal : Journal} (bounded : Extends journal (tree.journal Location.root))
    (causal : tree.Causal Location.root journal) (activated : route.Activated journal) :
    (route.Ready journal ∧ OpenParent journal target) ∨ Obsolete journal target := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  rcases route.activated_cases expansion rootSize (fun _ h => h) rootSize bounded causal activated with ready | obsolete
  · exact .inl ⟨ready, ready.open_parent rootSize (by simp [OpenParent, Location.root, Location.parent?])⟩
  · exact .inr obsolete

/-- Every tree has an immediately activated entry command. Delays require no
durable record and are traversed before that first command. -/
theorem ExecutionTree.entry_activated (tree : ExecutionTree) (current : Location) (journal : Journal) :
    ∃ node, ∃ route : TreeRoute tree current current node, route.Activated journal := by
  cases tree with
  | terminal result => exact ⟨_, .terminal result current, trivial⟩
  | fork children result next => exact ⟨_, .fork children result next current, trivial⟩
  | delay rest =>
    obtain ⟨node, route, activated⟩ := rest.entry_activated current journal
    exact ⟨node, .delay route, activated⟩

end LeanCloud.Proofs
