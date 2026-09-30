import LeanCloud.Proofs.TreeJournal
import LeanCloud.Proofs.CompletionView

/-! Database safety stated against the program's own execution tree. Missing
records are allowed; every present record must have its program-defined value. -/

universe u

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery

/-- A partial group contains only the outcomes of its original indexed children. -/
def ExecutionTree.PartialSlots (children : List ExecutionTree) (slots : Array (Option Exit)) : Prop :=
  slots.size = children.length ∧ ∀ index : Fin children.length,
    slots[index.val]! = none ∨ slots[index.val]! = some children[index.val].exit

/-- The logical writes permitted at one command. A group's cached result and
each present child slot are prescribed by the pure program. -/
def ExecutionTree.Admits (node : ExecutionTree) (record : Result) : Prop :=
  match node, record with
  | .terminal outcome, .completed result => result = encodeOutcome (inferInstance : Codec Json) outcome
  | .fork _ outcome _, .completed result => result = encodeOutcome (inferInstance : Codec Json) outcome
  | .fork children _ _, .suspended slots => PartialSlots children slots
  | _, _ => False

theorem ExecutionTree.PartialSlots.empty (children : List ExecutionTree) :
    PartialSlots children (Array.replicate children.length none) := by
  refine ⟨by simp, ?_⟩
  intro index
  exact .inl (by simp)

/-- Settling a valid partial array either retains that partial array or yields
exactly the pure fork result, including the original array-order failure. -/
theorem Expansion.settle_admitted {m : Type → Type u} {program : Cloud m Json} {children result next slots}
    (expansion : Expansion program (.fork children result next))
    (valid : ExecutionTree.PartialSlots children slots) :
    (ExecutionTree.fork children result next).Admits (Result.settle slots) := by
  by_cases missing : none ∈ slots
  · rw [Result.settle_missing slots missing]
    exact valid
  · have full : slots = ExecutionTree.slots children := by
      apply Array.ext
      · simpa [ExecutionTree.slots] using valid.1
      · intro index inside _
        have bound : index < children.length := by simpa only [valid.1] using inside
        rcases valid.2 ⟨index, bound⟩ with absent | present
        · exact False.elim (missing (by
            have absent' : slots[index] = none := by simpa only [getElem!_pos slots index inside] using absent
            rw [← absent']
            exact Array.getElem_mem inside))
        · simpa [ExecutionTree.slots, getElem!_pos, inside] using present
    rw [full, expansion.fork_result]
    rfl

/-- Admitted logical writes expand only to this node's immutable physical fields. -/
theorem ExecutionTree.Admits.records {node : ExecutionTree} {record : Result}
    (admitted : node.Admits record) (location : Location) :
    JournalAdapter.records location.key record ⊆ node.ownRecords location := by
  cases node with
  | delay _ => cases record <;> cases admitted
  | terminal outcome =>
    cases record with
    | suspended _ => cases admitted
    | completed result =>
      cases admitted
      exact fun _ h => h
  | fork children outcome next =>
    cases record with
    | completed result =>
      cases admitted
      intro entry member
      simp only [JournalAdapter.records, List.mem_singleton] at member
      subst entry
      simp [ownRecords]
    | suspended slots =>
      obtain ⟨size, allowed⟩ := admitted
      intro entry member
      rcases List.mem_cons.mp member with descriptor | child
      · subst entry
        simp [ownRecords, size]
      · obtain ⟨index, inside, published⟩ := List.mem_filterMap.mp child
        have bound : index < children.length := by simpa [size] using List.mem_range.mp inside
        rcases allowed ⟨index, bound⟩ with missing | recorded
        · simp [childRecord, missing] at published
        · simp only [childRecord, recorded, Option.map_some, Option.some.injEq] at published
          subst entry
          simp only [ownRecords, List.mem_cons, List.mem_ofFn]
          exact .inr (.inr ⟨⟨index, bound⟩, rfl⟩)

/-- Same-value agreement for a save follows from its program node. The only
comparison law needed here is reflexivity on the program's encoded records. -/
theorem ExecutionTree.admitted_agrees {tree node : ExecutionTree} {root location : Location} {record}
    (nonempty : 0 < root.size) (member : (location, node) ∈ tree.nodes root)
    (admitted : node.Admits record) (comparable : Comparable (tree.journal root)) :
    Agrees (JournalAdapter.records location.key record) (tree.journal root) := by
  intro entry published
  have recorded := tree.journal_contains root nonempty entry
    (ExecutionTree.ownRecords_subset member (admitted.records location published))
  exact ⟨recorded, comparable _ _ recorded⟩

/-- Proof description of the currently present slots. Their values come from
the program; the durable journal determines only which ones are present. -/
def ExecutionTree.observedSlots (children : List ExecutionTree) (journal : Journal) (location : Location) :
    Array (Option Exit) := Array.ofFn fun index : Fin children.length =>
  match journal (childKey location.key index.val) with
  | none => none
  | some _ => some children[index.val].exit

theorem ExecutionTree.observedSlots_spec {tree : ExecutionTree} {root location : Location}
    {children result next} (nonempty : 0 < root.size)
    (member : (location, .fork children result next) ∈ tree.nodes root)
    (journal : Journal) (bounded : Extends journal (tree.journal root)) :
    PartialSlots children (observedSlots children journal location) ∧
      ∀ i, i < children.length → journal (childKey location.key i) =
        (observedSlots children journal location)[i]!.map toJson := by
  have fields := (tree.fork_fields nonempty member).2.2
  constructor
  · refine ⟨by simp [observedSlots], ?_⟩
    intro index
    cases recorded : journal (childKey location.key index.val) <;>
      simp [observedSlots, recorded]
  · intro index inside
    cases recorded : journal (childKey location.key index) with
    | none => simp [observedSlots, inside, recorded]
    | some value =>
      have same := (bounded _ _ recorded).symm.trans (fields ⟨index, inside⟩)
      cases same
      simp [observedSlots, inside, recorded]

/-- Reading any sparse, compatible fork journal yields a valid partial group
or the program's completed fork result. No successful replay is assumed. -/
theorem Expansion.fork_view {m : Type → Type u} {program : Cloud m Json} {tree : ExecutionTree}
    (expansion : Expansion program tree) {root location : Location} {children result next}
    (nonempty : 0 < root.size) (member : (location, .fork children result next) ∈ tree.nodes root)
    (journal : Journal) (bounded : Extends journal (tree.journal root)) :
    ∃ record : Option Result, JournalDb.get raw location.key journal = (record.map toJson, journal) ∧
      ∀ value ∈ record, (ExecutionTree.fork children result next).Admits value := by
  obtain ⟨descriptor, expected, _⟩ := tree.fork_fields nonempty member
  cases cached : journal (resultKey location.key) with
  | some value =>
    have same := (bounded _ _ cached).symm.trans expected
    cases same
    refine ⟨some (.completed (encodeOutcome (inferInstance : Codec Json) result)),
      get_completed _ _ _ cached, ?_⟩
    intro value same
    cases same
    rfl
  | none =>
    cases recorded : journal (forkKey location.key) with
    | none => exact ⟨none, get_missing _ _ cached recorded, by simp⟩
    | some value =>
      have same := (bounded _ _ recorded).symm.trans descriptor
      cases same
      let slots := ExecutionTree.observedSlots children journal location
      obtain ⟨valid, slotRecords⟩ := tree.observedSlots_spec nonempty member journal bounded
      obtain ⟨subprogram, subexpansion⟩ := expansion.node member
      refine ⟨some (Result.settle slots), get_fork journal location.key slots cached ?_ ?_, ?_⟩
      · simpa only [slots, ExecutionTree.observedSlots, Array.size_ofFn] using recorded
      · intro i inside
        exact slotRecords i (by simpa only [slots, ExecutionTree.observedSlots, Array.size_ofFn] using inside)
      · intro value same
        cases same
        exact subexpansion.settle_admitted valid

end LeanCloud.Proofs
