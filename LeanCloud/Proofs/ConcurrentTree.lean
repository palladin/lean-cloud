import LeanCloud.Proofs.ConcurrentFinish
import LeanCloud.Proofs.TreeRecovery
import LeanCloud.Proofs.TreeCompletion
import LeanCloud.Proofs.TreeSnapshot

/-! The pure program supplies the record contracts used by concurrent workers.
The expected journal is a specification extracted from the execution tree, not
preloaded storage and not an assumption about a completed replay execution. -/

universe u

namespace LeanCloud.Proofs
open Lean JournalDb JournalLayout JournalAdapter ReplayRecovery ConcurrentJournal SimulationBackend

/-- Every physical record in a pure execution tree has the adapter's required
encoding, including when the queried location is not a node of that tree. -/
theorem ExecutionTree.readable (tree : ExecutionTree) (root : Location)
    (nonempty : 0 < root.size) (key : String) : Readable (tree.journal root) key := by
  have entry field value (stored : tree.journal root field = some value) :
      ∃ (location : Location) (node : ExecutionTree), (field, value) ∈ node.ownRecords location := by
    obtain ⟨⟨location, node⟩, _, member⟩ :=
      List.mem_flatMap.mp ((tree.journal_read_iff root nonempty field value).mp stored)
    exact ⟨location, node, member⟩
  constructor
  · intro value stored
    obtain ⟨location, node, member⟩ := entry _ _ stored
    cases node with
    | terminal result =>
      simp only [ownRecords, List.mem_singleton, Prod.mk.injEq] at member
      exact ⟨_, member.2⟩
    | delay _ => simp [ownRecords] at member
    | fork children result next =>
      simp only [ownRecords, List.mem_cons, List.mem_ofFn, Prod.mk.injEq] at member
      rcases member with ⟨same, _⟩ | ⟨_, value⟩ | ⟨index, same, _⟩
      · exact False.elim (result_ne_fork _ _ same)
      · exact ⟨_, value⟩
      · exact False.elim (result_ne_child _ _ _ same.symm)
  · intro value stored
    obtain ⟨location, node, member⟩ := entry _ _ stored
    cases node with
    | terminal result =>
      simp only [ownRecords, List.mem_singleton, Prod.mk.injEq] at member
      exact False.elim (result_ne_fork _ _ member.1.symm)
    | delay _ => simp [ownRecords] at member
    | fork children result next =>
      simp only [ownRecords, List.mem_cons, List.mem_ofFn, Prod.mk.injEq] at member
      rcases member with ⟨_, value⟩ | ⟨same, _⟩ | ⟨index, same, _⟩
      · exact ⟨_, value⟩
      · exact False.elim (result_ne_fork _ _ same.symm)
      · exact False.elim (fork_ne_child _ _ _ same.symm)
  · intro index value stored
    obtain ⟨location, node, member⟩ := entry _ _ stored
    cases node with
    | terminal result =>
      simp only [ownRecords, List.mem_singleton, Prod.mk.injEq] at member
      exact False.elim (result_ne_child _ _ _ member.1.symm)
    | delay _ => simp [ownRecords] at member
    | fork children result next =>
      simp only [ownRecords, List.mem_cons, List.mem_ofFn, Prod.mk.injEq] at member
      rcases member with ⟨same, _⟩ | ⟨same, _⟩ | ⟨child, _, value⟩
      · exact False.elim (fork_ne_child _ _ _ same.symm)
      · exact False.elim (result_ne_child _ _ _ same.symm)
      · exact ⟨_, value.symm⟩

/-- A logical record assembled from the program's prescribed fields contains
only the original command result or the original indexed child outcomes. -/
theorem ExecutionTree.published_admitted {tree node : ExecutionTree} {root location : Location}
    (nonempty : 0 < root.size) (member : (location, node) ∈ tree.nodes root)
    {record : Result}
    (published : JournalAdapter.Published (JournalAdapter.records location.key record) (tree.journal root)) :
    node.Admits record := by
  cases record with
  | completed outcome =>
    have stored := published (resultKey location.key, toJson outcome) (by simp [JournalAdapter.records])
    rw [tree.node_field_read nonempty member (.inl rfl)] at stored
    cases node with
    | delay _ => simp [ownRecords] at stored
    | terminal result | fork children result next =>
      simp only [ownRecords, List.lookup_cons, beq_self_eq_true, beq_eq_false_iff_ne.mpr (result_ne_fork location.key location.key)] at stored
      exact toJson_injective exit_roundtrip (Option.some.inj stored).symm
  | suspended slots =>
    obtain ⟨fork, childrenStored⟩ := published_fork published
    have descriptor := tree.node_field_read nonempty member (key := forkKey location.key) (.inr (.inl rfl))
    cases node with
    | delay _ => simp [descriptor, ownRecords] at fork
    | terminal result =>
      rw [descriptor] at fork
      simp [ownRecords, List.lookup_cons,
        beq_eq_false_iff_ne.mpr (result_ne_fork location.key location.key).symm] at fork
    | fork children result next =>
      have fields := tree.fork_fields nonempty member
      have size : slots.size = children.length := toJson_injective (α := Nat) (fun _ => rfl)
        (Option.some.inj (fork.symm.trans fields.1))
      refine ⟨size, ?_⟩
      intro index
      cases slot : slots[index.val]! with
      | none => exact .inl rfl
      | some outcome =>
        have stored := childrenStored index.val (by rw [size]; exact index.isLt) outcome slot
        have same : outcome = children[index.val].exit := toJson_injective exit_roundtrip
          (Option.some.inj (stored.symm.trans (fields.2.2 index)))
        exact .inr (congrArg some same)

/-- Cached group outcomes and child slots agree because they come from the
same pure fork, using the runtime's array-order result selection. -/
theorem Expansion.coherent {m : Type → Type u} {program : Cloud m Json} {tree node : ExecutionTree}
    (expansion : Expansion program tree) {root location : Location}
    (nonempty : 0 < root.size) (member : (location, node) ∈ tree.nodes root) :
    Coherent (tree.journal root) location.key := by
  intro slots outcome published settled
  have validSlots := tree.published_admitted nonempty member published
  cases node with
  | terminal _ | delay _ => cases validSlots
  | fork children result next =>
    obtain ⟨program, expanded⟩ := expansion.node member
    have admitted := expanded.settle_admitted validSlots
    rw [settled] at admitted
    cases admitted
    exact (tree.fork_fields nonempty member).2.1

/-- A concurrent read may be stale or mix observation times, but every result
it returns is still admitted by this command in the original pure program. -/
theorem ConcurrentJournal.ReadResult.admitted {m : Type → Type u} {program : Cloud m Json}
    {tree node : ExecutionTree} (expansion : Expansion program tree) {root location : Location}
    (nonempty : 0 < root.size) (member : (location, node) ∈ tree.nodes root)
    {before after : Durable} {answer : Option Result}
    (seen : ReadResult location.key before after answer)
    (bounded : ConcurrentJournal.Valid (tree.journal root) after) :
    ∀ record ∈ answer, node.Admits record := by
  cases seen with
  | missing _ _ => simp
  | completed outcome completed =>
    intro record same
    cases same
    apply tree.published_admitted nonempty member
    intro entry stored
    simp only [JournalAdapter.records, List.mem_singleton] at stored
    subst entry
    exact completed_intended (expansion.coherent nonempty member) bounded completed
  | suspended slots published _ _ =>
    intro record same
    cases same
    exact tree.published_admitted nonempty member (fun entry included => bounded _ _ (published entry included))

/-- The entire actual completion call, with value agreement, readable records,
and cache consistency derived from the program. Parent descriptors and readiness
are durable prerequisites, to be established by reconstruction and queue delivery. -/
theorem TreeRoute.finish_tree_checked {program : Cloud M Json} {tree current node}
    (expansion : Expansion program tree) (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (initial : Durable) (bounded : ConcurrentJournal.Valid (tree.journal Location.root) initial)
    (ready : node.FinishReady current (ConcurrentJournal.view initial))
    (descriptors : ∀ parent index, current.parent? = some (parent, index) →
      ∃ count : Nat, ConcurrentJournal.view initial (forkKey parent.key) = some (toJson count)) :
    Checked (tree.journal Location.root)
      (ReplayInterpreter.Internal.finish (JournalDb.ofDb rawDb) current node.exit)
      (Finished current node.exit initial) initial := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  have intended : tree.journal Location.root (resultKey current.key) = some (toJson node.exit) := by
    apply tree.journal_contains Location.root rootSize (resultKey current.key, toJson node.exit)
    exact ExecutionTree.ownRecords_subset route.member
      (ready.admitted.records current (by simp [JournalAdapter.records]))
  apply finish_checked (tree.journal Location.root) current node.exit
    (tree.readable _ rootSize _) (expansion.coherent rootSize route.member) comparable sameExit intended
    initial initial bounded (.refl _) (tree.finish_source rootSize route.member bounded ready)
  intro parent index linked
  obtain ⟨children, result, next, inside, member, outcome⟩ := route.child_outcome linked
  obtain ⟨count, descriptor⟩ := descriptors parent index linked
  have fields := tree.fork_fields rootSize member
  have size : count = children.length := toJson_injective (α := Nat) (fun _ => rfl)
    (Option.some.inj ((bounded _ _ descriptor).symm.trans fields.1))
  refine ⟨count, by omega, descriptor, ?_, tree.readable _ rootSize _, expansion.coherent rootSize member⟩
  simpa only [outcome] using fields.2.2 ⟨index, inside⟩

end LeanCloud.Proofs
