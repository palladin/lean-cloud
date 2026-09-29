import LeanCloud.Proofs.TreeRecovery

/-! Recover physical slot facts from a logical suspended-group read. These
facts are used to construct completion layouts from the current journal. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery

private theorem view_unique {journal : Journal} {key : String} {first second : Result}
    (left : JournalDb.get raw key journal = (some (toJson first), journal))
    (right : JournalDb.get raw key journal = (some (toJson second), journal)) : first = second := by
  exact toJson_injective result_roundtrip (Option.some.inj (congrArg Prod.fst (left.symm.trans right)))

/-- A suspended read identifies the actual descriptor and every physical slot.
This derives a layout from storage instead of assuming the worker's response. -/
theorem ExecutionTree.suspended_snapshot {tree : ExecutionTree} {root parent : Location}
    {children result next slots} (nonempty : 0 < root.size)
    (member : (parent, .fork children result next) ∈ tree.nodes root)
    (journal : Journal) (bounded : Extends journal (tree.journal root))
    (view : JournalDb.get raw parent.key journal = (some (toJson (Result.suspended slots)), journal)) :
    journal (resultKey parent.key) = none ∧
      journal (forkKey parent.key) = some (toJson slots.size) ∧
      PartialSlots children slots ∧
      ∀ index, index < slots.size → journal (childKey parent.key index) = slots[index]!.map toJson := by
  obtain ⟨descriptor, expected, _⟩ := tree.fork_fields nonempty member
  cases cached : journal (resultKey parent.key) with
  | some value =>
    have same := (bounded _ _ cached).symm.trans expected
    cases same
    have impossible := view_unique (get_completed _ _ _ cached) view
    cases impossible
  | none =>
    cases recorded : journal (forkKey parent.key) with
    | none =>
      have impossible := (get_missing journal parent.key cached recorded).symm.trans view
      cases impossible
    | some value =>
      have same := (bounded _ _ recorded).symm.trans descriptor
      cases same
      obtain ⟨valid, physical⟩ := tree.observedSlots_spec nonempty member journal bounded
      have observed := get_fork journal parent.key (observedSlots children journal parent) cached
        (by simpa [observedSlots] using recorded) (by
          intro i inside
          exact physical i (by simpa [observedSlots] using inside))
      have same := Result.settle_suspended (view_unique observed view)
      rw [same] at valid physical
      exact ⟨rfl, by simp only [valid.1], valid,
        fun i inside => physical i (by simpa only [valid.1] using inside)⟩

/-- Exact preservation of a group's physical fields preserves its suspended
logical read. This also accounts for the adapter's settling of child slots. -/
theorem ExecutionTree.suspended_frame {tree : ExecutionTree} {root parent : Location}
    {children result next slots before after} (nonempty : 0 < root.size)
    (member : (parent, .fork children result next) ∈ tree.nodes root)
    (bounded : Extends before (tree.journal root))
    (view : JournalDb.get raw parent.key before = (some (toJson (Result.suspended slots)), before))
    (cache : after (resultKey parent.key) = before (resultKey parent.key))
    (fork : after (forkKey parent.key) = before (forkKey parent.key))
    (child : ∀ index, index < slots.size → after (childKey parent.key index) = before (childKey parent.key index)) :
    JournalDb.get raw parent.key after = (some (toJson (Result.suspended slots)), after) := by
  obtain ⟨uncached, descriptor, _, physical⟩ := tree.suspended_snapshot nonempty member before bounded view
  have settled := view_unique (get_fork before parent.key slots uncached descriptor physical) view
  have observed := get_fork after parent.key slots (cache.trans uncached) (fork.trans descriptor)
    (fun index inside => (child index inside).trans (physical index inside))
  simpa only [settled] using observed

theorem ExecutionTree.PartialSlots.set {children : List ExecutionTree} {slots : Array (Option Exit)}
    (valid : PartialSlots children slots) (index : Fin children.length) :
    PartialSlots children (slots.set! index.val (some children[index.val].exit)) := by
  refine ⟨by simpa using valid.1, ?_⟩
  intro other
  have inside : index.val < slots.size := by rw [valid.1]; exact index.isLt
  by_cases same : other.val = index.val
  · have identical : other = index := Fin.ext same
    subst other
    exact .inr (Array.getElem!_set!_self _ _ _ inside)
  · have bound : other.val < slots.size := by rw [valid.1]; exact other.isLt
    simpa [getElem!_pos, bound, Ne.symm same] using valid.2 other

/-- Clearing only the selected proof slot lets one layout handle both a first
completion and redelivery after that slot was already committed. -/
theorem ExecutionTree.PartialSlots.clear {children : List ExecutionTree} {slots : Array (Option Exit)}
    (valid : PartialSlots children slots) (index : Fin children.length) :
    PartialSlots children (slots.set! index.val none) := by
  refine ⟨by simpa using valid.1, ?_⟩
  intro other
  have inside : index.val < slots.size := by rw [valid.1]; exact index.isLt
  by_cases same : other.val = index.val
  · have identical : other = index := Fin.ext same
    subst other
    exact .inl (Array.getElem!_set!_self _ _ _ inside)
  · have bound : other.val < slots.size := by rw [valid.1]; exact other.isLt
    simpa [getElem!_pos, bound, Ne.symm same] using valid.2 other

/-- A completed fork read has durable evidence: its cache or all its child
slots. This derives the completion-source premise needed by recovery. -/
theorem ExecutionTree.fork_completed_at {tree : ExecutionTree} {root current : Location}
    {children result next outcome} (nonempty : 0 < root.size)
    (member : (current, .fork children result next) ∈ tree.nodes root)
    (journal : Journal) (bounded : Extends journal (tree.journal root))
    (view : JournalDb.get raw current.key journal = (some (toJson (Result.completed outcome)), journal)) :
    CompletedAt journal current.key outcome := by
  obtain ⟨descriptor, expected, _⟩ := tree.fork_fields nonempty member
  cases cached : journal (resultKey current.key) with
  | some value =>
    have same := (bounded _ _ cached).symm.trans expected
    cases same
    have identical := Result.completed.inj (view_unique (get_completed _ _ _ cached) view)
    subst outcome
    exact .cached cached
  | none =>
    cases recorded : journal (forkKey current.key) with
    | none =>
      have impossible := (get_missing journal current.key cached recorded).symm.trans view
      cases impossible
    | some value =>
      have same := (bounded _ _ recorded).symm.trans descriptor
      cases same
      let slots := observedSlots children journal current
      obtain ⟨valid, physical⟩ := tree.observedSlots_spec nonempty member journal bounded
      have observed := get_fork journal current.key slots cached
        (by simpa [slots, observedSlots] using recorded) (by
          intro i inside
          exact physical i (by simpa [slots, observedSlots] using inside))
      have settled := view_unique observed view
      refine .group slots (by simpa [slots, observedSlots] using recorded) ?_ settled
      intro i inside
      cases slot : slots[i]! with
      | some value =>
        refine ⟨value, rfl, ?_⟩
        have physicalSlot : journal (childKey current.key i) = slots[i]!.map toJson :=
          physical i (by simpa [slots, observedSlots] using inside)
        simpa only [slot, Option.map_some] using physicalSlot
      | none =>
        have missing : none ∈ slots := by
          have same : slots[i] = none := by simpa only [getElem!_pos slots i inside] using slot
          rw [← same]
          exact Array.getElem_mem inside
        rw [Result.settle_missing slots missing] at settled
        cases settled

/-- Once a fork has completed, compatible immutable additions cannot make a
later read suspended or change its outcome. -/
theorem ExecutionTree.fork_completed_grow {tree : ExecutionTree} {root current : Location}
    {children result next outcome} (nonempty : 0 < root.size)
    (member : (current, .fork children result next) ∈ tree.nodes root)
    {before after : Journal} (growth : Extends before after) (bounded : Extends after (tree.journal root))
    (intended : (ExecutionTree.fork children result next).Admits (.completed outcome))
    (view : JournalDb.get raw current.key before = (some (toJson (Result.completed outcome)), before)) :
    JournalDb.get raw current.key after = (some (toJson (Result.completed outcome)), after) := by
  have recorded := tree.fork_completed_at nonempty member before (growth.trans bounded) view
  apply (recorded.grow growth).view bounded
  cases intended
  exact (tree.fork_fields nonempty member).2.1

/-- A terminal command can finish immediately; a fork without a continuation
can finish after its group outcome is durable. Successful forks with a next
command resume that continuation instead of completing the branch. -/
def ExecutionTree.FinishReady (node : ExecutionTree) (current : Location) (journal : Journal) : Prop :=
  match node with
  | .terminal _ => True
  | .fork _ _ none =>
    JournalDb.get raw current.key journal = (some (toJson (Result.completed node.exit)), journal)
  | _ => False

theorem ExecutionTree.FinishReady.admitted {node : ExecutionTree} {current : Location} {journal : Journal}
    (ready : node.FinishReady current journal) : node.Admits (.completed node.exit) := by
  cases node with
  | terminal _ => rfl
  | delay _ => cases ready
  | fork children result next => cases next with
    | none => rfl
    | some _ => cases ready

theorem ExecutionTree.finish_source {tree node : ExecutionTree} {root current : Location}
    (nonempty : 0 < root.size) (member : (current, node) ∈ tree.nodes root)
    {journal : Journal} (bounded : Extends journal (tree.journal root))
    (ready : node.FinishReady current journal) :
    CompletionSource journal (tree.journal root) current.key node.exit := by
  cases node with
  | terminal _ => exact .terminal (tree.terminal_fields nonempty member).2
  | delay _ => cases ready
  | fork children result next => cases next with
    | none => exact (tree.fork_completed_at nonempty member journal bounded ready).source
    | some _ => cases ready

theorem ExecutionTree.FinishReady.grow {tree node : ExecutionTree} {root current : Location}
    (nonempty : 0 < root.size) (member : (current, node) ∈ tree.nodes root)
    {before after : Journal} (ready : node.FinishReady current before)
    (growth : Extends before after) (bounded : Extends after (tree.journal root)) :
    node.FinishReady current after := by
  cases node with
  | terminal _ => trivial
  | delay _ => cases ready
  | fork children result next => cases next with
    | none => exact tree.fork_completed_grow nonempty member growth bounded ready.admitted ready
    | some _ => cases ready

/-- A live child can still publish into its parent's suspended group. -/
def OpenParent (journal : Journal) (current : Location) : Prop :=
  ∀ parent index, current.parent? = some (parent, index) →
    ∃ slots : Array (Option Exit), JournalDb.get raw parent.key journal =
      (some (toJson (Result.suspended slots)), journal)

end LeanCloud.Proofs
