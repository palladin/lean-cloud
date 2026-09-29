import LeanCloud.Proofs.TreeRecovery
import LeanCloud.Proofs.CompletionJournal

/-! Causal dependencies of physical records. A published child result certifies
completion of that child's entire pure subtree, including its nested forks.
These are predicates on durable data, not extra runtime records. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter JournalLayout ReplayRecovery

/-- A branch is complete when every command in its pure execution tree has
durable completion evidence. A full fork need not have a cached result. -/
def ExecutionTree.Completed (tree : ExecutionTree) (entry : Location) (journal : Journal) : Prop :=
  ∀ location node, (location, node) ∈ tree.nodes entry →
    ∃ outcome, node.Admits (.completed outcome) ∧ CompletedAt journal location.key outcome

theorem ExecutionTree.Completed.grow {tree : ExecutionTree} {entry : Location} {before after : Journal}
    (completed : tree.Completed entry before) (growth : Extends before after) : tree.Completed entry after := by
  intro location node member
  obtain ⟨outcome, admitted, recorded⟩ := completed location node member
  exact ⟨outcome, admitted, recorded.grow growth⟩

theorem ExecutionTree.completed_view {tree node : ExecutionTree} {root location : Location}
    (nonempty : 0 < root.size) (member : (location, node) ∈ tree.nodes root)
    {journal : Journal} (bounded : Extends journal (tree.journal root))
    {outcome : Exit} (admitted : node.Admits (.completed outcome))
    (recorded : CompletedAt journal location.key outcome) :
    JournalDb.get raw location.key journal = (some (toJson (Result.completed outcome)), journal) := by
  apply recorded.view bounded
  exact tree.journal_contains root nonempty (resultKey location.key, toJson outcome)
    (ExecutionTree.ownRecords_subset member (admitted.records location (by simp [JournalAdapter.records])))

/-- Prerequisites for publishing one physical key. A fork cache requires its
children to have finished; a child slot requires that particular child to have
finished. Descriptors and terminal caches have no completion prerequisites. -/
def ExecutionTree.Requires (tree : ExecutionTree) (root : Location) (key : String) (journal : Journal) : Prop :=
  ∀ location children result next,
    (location, ExecutionTree.fork children result next) ∈ tree.nodes root →
      (key = resultKey location.key → ∀ index : Fin children.length,
        children[index.val].Completed (location.child index.val) journal) ∧
      (∀ index : Fin children.length, key = childKey location.key index.val →
        children[index.val].Completed (location.child index.val) journal)

theorem ExecutionTree.Requires.grow {tree : ExecutionTree} {root : Location} {key : String}
    {before after : Journal} (required : tree.Requires root key before) (growth : Extends before after) :
    tree.Requires root key after := by
  intro location children result next member
  obtain ⟨cache, slot⟩ := required location children result next member
  exact ⟨fun same index => (cache same index).grow growth,
    fun index same => (slot index same).grow growth⟩

/-- Every present physical record has its completion prerequisites. Value
agreement with the program's journal is a separate invariant. -/
def ExecutionTree.Causal (tree : ExecutionTree) (root : Location) (journal : Journal) : Prop :=
  ∀ key value, journal key = some value → tree.Requires root key journal

theorem ExecutionTree.Causal.empty (tree : ExecutionTree) (root : Location) : tree.Causal root Journal.empty := by
  intro key value recorded
  cases recorded

/-- Adding an agreed record whose prerequisites already hold preserves the
causal invariant. This covers both sides of a primitive write's crash boundary. -/
theorem ExecutionTree.Causal.write {tree : ExecutionTree} {root : Location} {journal expected : Journal}
    (causal : tree.Causal root journal) (bounded : Extends journal expected) {key value}
    (intended : expected key = some value) (required : tree.Requires root key journal) :
    tree.Causal root (journal.write key value) := by
  have growth := (extends_write bounded intended).1
  intro other stored present
  by_cases same : other = key
  · subst other
    exact required.grow growth
  · rw [Journal.read_write_other _ _ _ _ same] at present
    exact (causal other stored present).grow growth

/-- Causality survives an interval of immutable additions when the possible
new keys have their prerequisites in the interval's lower bound. -/
theorem ExecutionTree.Causal.between {tree : ExecutionTree} {root : Location} {initial expected journal : Journal}
    (causal : tree.Causal root initial) (interval : Between initial expected journal)
    (required : ∀ key value, expected key = some value → initial key = none → tree.Requires root key initial) :
    tree.Causal root journal := by
  intro key value recorded
  cases old : initial key with
  | some previous => exact (causal key previous old).grow interval.1
  | none => exact (required key value (interval.2 _ _ recorded) old).grow interval.1

theorem ExecutionTree.requires_descriptor (tree : ExecutionTree) (root location : Location) (journal : Journal) :
    tree.Requires root (forkKey location.key) journal := by
  intro other children result next member
  exact ⟨fun same => False.elim (result_ne_fork _ _ same.symm),
    fun index same => False.elim (fork_ne_child _ _ _ same)⟩

theorem ExecutionTree.requires_terminal {tree : ExecutionTree} {root location : Location} {outcome}
    (nonempty : 0 < root.size) (member : (location, .terminal outcome) ∈ tree.nodes root) (journal : Journal) :
    tree.Requires root (resultKey location.key) journal := by
  intro other children result next otherMember
  constructor
  · intro same
    have locations := Location.key_injective (tree.node_nonempty nonempty member)
      (tree.node_nonempty nonempty otherMember) (result_key_injective same)
    have nodes := tree.node_unique nonempty member otherMember locations
    cases nodes
  · intro index same
    exact False.elim (result_ne_child _ _ _ same)

theorem ExecutionTree.requires_cache {tree : ExecutionTree} {root location : Location} {children result next}
    (nonempty : 0 < root.size) (member : (location, .fork children result next) ∈ tree.nodes root)
    {journal : Journal} (finished : ∀ index : Fin children.length,
      children[index.val].Completed (location.child index.val) journal) :
    tree.Requires root (resultKey location.key) journal := by
  intro other descendants otherResult later otherMember
  constructor
  · intro same
    have locations := Location.key_injective (tree.node_nonempty nonempty member)
      (tree.node_nonempty nonempty otherMember) (result_key_injective same)
    have nodes := tree.node_unique nonempty member otherMember locations
    cases locations
    cases nodes
    exact finished
  · intro index same
    exact False.elim (result_ne_child _ _ _ same)

theorem ExecutionTree.requires_child {tree : ExecutionTree} {root location : Location} {children result next}
    (nonempty : 0 < root.size) (member : (location, .fork children result next) ∈ tree.nodes root)
    (index : Fin children.length) {journal : Journal}
    (finished : children[index.val].Completed (location.child index.val) journal) :
    tree.Requires root (childKey location.key index.val) journal := by
  intro other descendants otherResult later otherMember
  constructor
  · intro same
    exact False.elim (result_ne_child _ _ _ same.symm)
  · intro selected same
    obtain ⟨keys, indices⟩ := child_key_injective same
    have locations := Location.key_injective (tree.node_nonempty nonempty member)
      (tree.node_nonempty nonempty otherMember) keys
    have nodes := tree.node_unique nonempty member otherMember locations
    cases locations
    cases nodes
    have identical : index = selected := Fin.ext indices
    cases identical
    exact finished

/-- A completed group, cached or assembled from slots, certifies completed
subtrees for all its children. This is the dependency needed for stale work. -/
theorem ExecutionTree.Causal.completed_children {tree : ExecutionTree} {root location : Location}
    {children result next journal outcome}
    (causal : tree.Causal root journal) (nonempty : 0 < root.size)
    (member : (location, .fork children result next) ∈ tree.nodes root)
    (bounded : Extends journal (tree.journal root)) (completed : CompletedAt journal location.key outcome) :
    ∀ index : Fin children.length, children[index.val].Completed (location.child index.val) journal := by
  cases completed with
  | cached stored => exact (causal _ _ stored location children result next member).1 rfl
  | group slots fork filled settled =>
    have expected := (tree.fork_fields nonempty member).1
    have same := Option.some.inj ((bounded _ _ fork).symm.trans expected)
    have size : slots.size = children.length := toJson_injective (fun _ => rfl) same
    intro index
    obtain ⟨value, _, recorded⟩ := filled index.val (by rw [size]; exact index.isLt)
    exact (causal _ _ recorded location children result next member).2 index rfl

end LeanCloud.Proofs
