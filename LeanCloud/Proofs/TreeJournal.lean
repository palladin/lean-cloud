import LeanCloud.Proofs.TreeRecords
import LeanCloud.Proofs.JournalRecovery

/-! The pure program determines one finite, unambiguous physical journal.
This journal specifies admissible records; it is never installed into the Db. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalLayout JournalAdapter

private def FieldAt (location : Location) (key : String) : Prop :=
  key = resultKey location.key ∨ key = forkKey location.key ∨
    ∃ index, key = childKey location.key index

private theorem field_location {left right : Location} {key : String}
    (leftSize : 0 < left.size) (rightSize : 0 < right.size)
    (first : FieldAt left key) (second : FieldAt right key) : left = right := by
  apply Location.key_injective leftSize rightSize
  rcases first with result | fork | ⟨i, child⟩ <;>
    rcases second with result' | fork' | ⟨j, child'⟩
  · exact result_key_injective (result.symm.trans result')
  · exact False.elim (result_ne_fork _ _ (result.symm.trans fork'))
  · exact False.elim (result_ne_child _ _ _ (result.symm.trans child'))
  · exact False.elim (result_ne_fork _ _ (result'.symm.trans fork))
  · exact fork_key_injective (fork.symm.trans fork')
  · exact False.elim (fork_ne_child _ _ _ (fork.symm.trans child'))
  · exact False.elim (result_ne_child _ _ _ (result'.symm.trans child))
  · exact False.elim (fork_ne_child _ _ _ (fork'.symm.trans child))
  · exact (child_key_injective (child.symm.trans child')).1

private theorem ownRecords_field {tree : ExecutionTree} {location : Location} {entry}
    (member : entry ∈ tree.ownRecords location) : FieldAt location entry.1 := by
  cases tree with
  | terminal result =>
    simp only [ExecutionTree.ownRecords, List.mem_singleton] at member
    exact .inl (congrArg Prod.fst member)
  | delay rest => simp [ExecutionTree.ownRecords] at member
  | fork children result next =>
    simp only [ExecutionTree.ownRecords, List.mem_cons, List.mem_ofFn] at member
    rcases member with rfl | rfl | ⟨index, rfl⟩
    · exact .inr (.inl rfl)
    · exact .inl rfl
    · exact .inr (.inr ⟨index.val, rfl⟩)

private theorem ownRecords_distinct (tree : ExecutionTree) (location : Location) :
    (tree.ownRecords location).Pairwise (fun left right => left.1 ≠ right.1) := by
  cases tree with
  | terminal _ => simp [ExecutionTree.ownRecords]
  | delay _ => simp [ExecutionTree.ownRecords]
  | fork children result next =>
    simp only [ExecutionTree.ownRecords, List.pairwise_cons]
    refine ⟨?_, ?_, ?_⟩
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact (result_ne_fork _ _).symm
      · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
        exact fork_ne_child _ _ _
    · intro entry member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact result_ne_child _ _ _
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj before equal
      simp only [List.getElem_ofFn] at equal
      have := (child_key_injective equal).2
      omega

/-- No two records in the complete program specification use the same key. -/
theorem ExecutionTree.records_nodup (tree : ExecutionTree) (location : Location)
    (nonempty : 0 < location.size) : ((tree.records location).map Prod.fst).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map, ExecutionTree.records, List.pairwise_flatMap]
  refine ⟨fun node _ => ownRecords_distinct node.2 node.1, ?_⟩
  have unique := tree.locations_nodup location nonempty
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at unique
  apply unique.imp_of_mem
  intro left right leftMem rightMem different first firstMem second secondMem same
  apply different
  apply field_location (tree.node_nonempty nonempty leftMem) (tree.node_nonempty nonempty rightMem)
    (ownRecords_field firstMem)
  exact same ▸ ownRecords_field secondMem

/-- The complete expected journal is derived solely from the pure program's tree. -/
def ExecutionTree.journal (tree : ExecutionTree) (location : Location) : Journal :=
  fun key => (tree.records location).lookup key

private theorem lookup_of_mem {entries : List (String × Json)}
    (distinct : (entries.map Prod.fst).Nodup) {key value} (member : (key, value) ∈ entries) :
    entries.lookup key = some value := by
  induction entries with
  | nil => cases member
  | cons head tail ih =>
    obtain ⟨absent, rest⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp member with same | tailMember
    · subst head; simp
    · have different : key ≠ head.1 := by
        intro same
        apply absent
        exact List.mem_map.mpr ⟨(key, value), tailMember, same⟩
      rcases head with ⟨headKey, headValue⟩
      have test : (key == headKey) = false := beq_eq_false_iff_ne.mpr different
      simpa only [List.lookup_cons, test] using ih rest tailMember

/-- Every specified field can be read back at its own key, without being
shadowed by a different node or field. -/
theorem ExecutionTree.journal_contains (tree : ExecutionTree) (location : Location)
    (nonempty : 0 < location.size) : Published (tree.records location) (tree.journal location) := by
  intro entry member
  exact lookup_of_mem (tree.records_nodup location nonempty) member

theorem ExecutionTree.journal_read_iff (tree : ExecutionTree) (location : Location)
    (nonempty : 0 < location.size) (key : String) (value : Json) :
    tree.journal location key = some value ↔ (key, value) ∈ tree.records location := by
  constructor
  · intro recorded
    obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp recorded
    simp [same]
  · exact tree.journal_contains location nonempty (key, value)

theorem ExecutionTree.ownRecords_subset {tree node : ExecutionTree} {root location : Location}
    (member : (location, node) ∈ tree.nodes root) : node.ownRecords location ⊆ tree.records root := by
  intro entry field
  exact List.mem_flatMap.mpr ⟨(location, node), member, field⟩

private theorem node_field_mem {tree node : ExecutionTree} {root location : Location}
    (nonempty : 0 < root.size) (member : (location, node) ∈ tree.nodes root)
    {key value} (field : FieldAt location key) :
    (key, value) ∈ tree.records root ↔ (key, value) ∈ node.ownRecords location := by
  constructor
  · intro recorded
    obtain ⟨⟨other, otherNode⟩, owner, record⟩ := List.mem_flatMap.mp recorded
    have same := field_location (tree.node_nonempty nonempty member) (tree.node_nonempty nonempty owner)
      field (ownRecords_field record)
    have identical := tree.node_unique nonempty member owner same
    cases identical
    exact record
  · intro own
    exact ExecutionTree.ownRecords_subset member own

private theorem node_field_read {tree node : ExecutionTree} {root location : Location}
    (nonempty : 0 < root.size) (member : (location, node) ∈ tree.nodes root)
    {key} (field : FieldAt location key) :
    tree.journal root key = (node.ownRecords location).lookup key := by
  cases stored : (node.ownRecords location).lookup key with
  | some value =>
    obtain ⟨before, after, same, _⟩ := List.lookup_eq_some_iff.mp stored
    apply (tree.journal_read_iff root nonempty key value).mpr
    apply (node_field_mem nonempty member field).mpr
    simp [same]
  | none =>
    cases actual : tree.journal root key with
    | none => rfl
    | some value =>
      have own := (node_field_mem nonempty member field).mp
        ((tree.journal_read_iff root nonempty key value).mp actual)
      have distinct : ((node.ownRecords location).map Prod.fst).Nodup :=
        List.pairwise_map.mpr (ownRecords_distinct node location)
      have := lookup_of_mem distinct own
      simp [stored] at this

/-- The complete specification contains no descriptor at a terminal command. -/
theorem ExecutionTree.terminal_fields {tree : ExecutionTree} {root location : Location} {outcome}
    (nonempty : 0 < root.size) (member : (location, .terminal outcome) ∈ tree.nodes root) :
    tree.journal root (resultKey location.key) =
        some (toJson (encodeOutcome (inferInstance : Codec Json) outcome)) ∧
      tree.journal root (forkKey location.key) = none := by
  constructor
  · rw [node_field_read nonempty member (.inl rfl)]
    simp [ExecutionTree.ownRecords]
  · rw [node_field_read nonempty member (.inr (.inl rfl))]
    simp [ExecutionTree.ownRecords, (result_ne_fork location.key location.key).symm]

/-- The fork's descriptor, cache, and indexed child results are all fixed by
the program, independently of which subset has actually been published. -/
theorem ExecutionTree.fork_fields {tree : ExecutionTree} {root location : Location}
    {children result next} (nonempty : 0 < root.size)
    (member : (location, .fork children result next) ∈ tree.nodes root) :
    tree.journal root (forkKey location.key) = some (toJson children.length) ∧
      tree.journal root (resultKey location.key) =
        some (toJson (encodeOutcome (inferInstance : Codec Json) result)) ∧
      ∀ index : Fin children.length, tree.journal root (childKey location.key index.val) =
        some (toJson children[index.val].exit) := by
  have contains := tree.journal_contains root nonempty
  have subset := ExecutionTree.ownRecords_subset member
  refine ⟨contains (forkKey location.key, toJson children.length) (subset (by simp [ExecutionTree.ownRecords])),
    contains (resultKey location.key, toJson (encodeOutcome (inferInstance : Codec Json) result))
      (subset (by simp [ExecutionTree.ownRecords])), ?_⟩
  intro index
  apply contains (childKey location.key index.val, toJson children[index.val].exit) (subset ?_)
  simp only [ExecutionTree.ownRecords, List.mem_cons, List.mem_ofFn]
  exact .inr (.inr ⟨index, rfl⟩)

end LeanCloud.Proofs
