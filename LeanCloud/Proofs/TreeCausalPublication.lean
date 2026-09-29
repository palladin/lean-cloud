import LeanCloud.Proofs.TreeCausality
import LeanCloud.Proofs.JournalFrame

/-! Causal publication through the actual physical adapter. Completion
dependencies must hold before a record is published, and survive each commit. -/

namespace LeanCloud.Proofs
open Lean CrashRecovery JournalAdapter ReplayRecovery ReplayInterpreter.Internal

/-- Publication preserves causal dependencies at every primitive boundary.
The requested keys' prerequisites come from the initial durable state; immutable
growth keeps those witnesses valid throughout the publication loop. -/
theorem ExecutionTree.publication_causal (tree : ExecutionTree) (root : Location)
    (expected initial : Journal) (entries : List Record)
    (agrees : Agrees entries expected)
    (required : ∀ entry ∈ entries, tree.Requires root entry.1 initial) :
    Triple (fun journal => Between initial expected journal ∧ tree.Causal root journal)
      (publication entries)
      (fun _ journal => Between initial expected journal ∧ tree.Causal root journal)
      (fun journal => Between initial expected journal ∧ tree.Causal root journal) := by
  apply publication_preserves
  intro entry member journal kept
  have intended := (agrees entry member).1
  obtain ⟨growth, bounded⟩ := extends_write kept.1.2 intended
  exact ⟨kept.1.grow growth bounded,
    kept.2.write kept.1.2 intended ((required entry member).grow kept.1.1)⟩

/-- The actual interpreter save both publishes its requested records and
preserves causality. Interrupted saves preserve the same durable invariant. -/
theorem ExecutionTree.save_causal_under (tree : ExecutionTree) (root : Location)
    (expected initial : Journal) (location : Location) (record : Result)
    (agrees : Agrees (JournalAdapter.records location.key record) expected)
    (required : ∀ entry ∈ JournalAdapter.records location.key record, tree.Requires root entry.1 initial) :
    Spec (fun journal => Between initial expected journal ∧ tree.Causal root journal)
      (save db location record)
      (fun _ journal => Between initial expected journal ∧ tree.Causal root journal ∧
        Published (JournalAdapter.records location.key record) journal)
      (fun journal => Between initial expected journal ∧ tree.Causal root journal) := by
  have causal : Triple (fun journal => Between initial expected journal ∧ tree.Causal root journal)
      (call (save db location record))
      (fun _ journal => Between initial expected journal ∧ tree.Causal root journal)
      (fun journal => Between initial expected journal ∧ tree.Causal root journal) := by
    rw [call_save]
    exact ((tree.publication_causal root expected initial _ agrees required).map _).weaken
      (fun _ h => h) (fun _ _ ⟨_, _, kept⟩ => kept) (fun _ h => h)
  exact ((save_spec expected initial location record agrees).preserve causal).weaken
    (fun _ h => ⟨h.1, h⟩)
    (fun _ _ h => ⟨⟨h.1.1, h.1.2.1⟩, h.2.2, h.1.2.2⟩)
    (fun _ h => h.2)

theorem ExecutionTree.save_causal {tree node : ExecutionTree} {root location : Location} {record : Result}
    (nonempty : 0 < root.size) (member : (location, node) ∈ tree.nodes root)
    (admitted : node.Admits record) (comparable : Comparable (tree.journal root)) (initial : Journal)
    (required : ∀ entry ∈ JournalAdapter.records location.key record, tree.Requires root entry.1 initial) :
    Spec (fun journal => Between initial (tree.journal root) journal ∧ tree.Causal root journal)
      (save db location record)
      (fun _ journal => Between initial (tree.journal root) journal ∧ tree.Causal root journal ∧
        Published (JournalAdapter.records location.key record) journal)
      (fun journal => Between initial (tree.journal root) journal ∧ tree.Causal root journal) :=
  tree.save_causal_under root (tree.journal root) initial location record
    (tree.admitted_agrees nonempty member admitted comparable) required

/-- Creating a fork needs no completed-child witnesses: a nonempty fork writes
only its descriptor, while an empty fork has no children to finish. -/
theorem ExecutionTree.initial_fork_requires {tree : ExecutionTree} {root location : Location}
    {children result next} (nonempty : 0 < root.size)
    (member : (location, .fork children result next) ∈ tree.nodes root) (journal : Journal) :
    ∀ entry ∈ JournalAdapter.records location.key (Result.settle (Array.replicate children.length none)),
      tree.Requires root entry.1 journal := by
  cases children with
  | nil =>
    have noChildren : ∀ index : Fin 0, False := fun index => Fin.elim0 index
    intro entry stored
    simp [Result.settle, JournalAdapter.records, pure, Except.pure, Functor.map, Except.map] at stored
    subst entry
    exact tree.requires_cache nonempty member (fun index => False.elim (noChildren index))
  | cons head tail =>
    have missing : none ∈ Array.replicate (head :: tail).length (none : Option Exit) := by simp
    rw [Result.settle_missing _ missing]
    intro entry stored
    simp [JournalAdapter.records, JournalAdapter.childRecord] at stored
    rcases stored with same | ⟨index, inside, value, slot, _⟩
    · subst entry
      exact tree.requires_descriptor root location journal
    · simp [getElem!_pos, inside] at slot

theorem Expansion.initialize_fork_causal {m : Type → Type} {program : Cloud m Json}
    {tree : ExecutionTree} {root location : Location} {children result next}
    (expansion : Expansion program (.fork children result next))
    (nonempty : 0 < root.size) (member : (location, .fork children result next) ∈ tree.nodes root)
    (comparable : Comparable (tree.journal root)) (initial : Journal) :
    Spec (fun journal => Between initial (tree.journal root) journal ∧ tree.Causal root journal)
      (save db location (Result.settle (Array.replicate children.length none)))
      (fun _ journal => Between initial (tree.journal root) journal ∧ tree.Causal root journal ∧
        Published (JournalAdapter.records location.key (Result.settle (Array.replicate children.length none))) journal)
      (fun journal => Between initial (tree.journal root) journal ∧ tree.Causal root journal) :=
  tree.save_causal nonempty member (expansion.settle_admitted (ExecutionTree.PartialSlots.empty children))
    comparable initial (tree.initial_fork_requires nonempty member initial)

end LeanCloud.Proofs
