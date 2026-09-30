import LeanCloud.Proofs.TreeSuccessors

/-! Coverage of unfinished branches by durable transport messages. A leased
message still counts. A message below a completed parent can wake that parent
through the interpreter's obsolete-delivery shortcut. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery

/-- Zero or more completed-parent shortcuts, each justified by durable data.
This is a relation between locations, not another worker evaluator. -/
inductive WakePath (journal : Journal) : Location → Location → Prop where
  | here (location) : WakePath journal location location
  | parent {source parent target index outcome}
      (linked : source.parent? = some (parent, index))
      (completed : CompletedAt journal parent.key outcome)
      (rest : WakePath journal parent target) : WakePath journal source target

theorem WakePath.grow {before after source target} (path : WakePath before source target)
    (growth : Extends before after) : WakePath after source target := by
  induction path with
  | here location => exact .here location
  | parent linked completed rest ih => exact .parent linked (completed.grow growth) ih

/-- A child is no longer needed once its slot or the parent group's outcome is
durable. The latter also covers obsolete deliveries after a completed cache. -/
def ChildReported (journal : Journal) (parent : Location) (index : Nat) (outcome : Exit) : Prop :=
  journal (childKey parent.key index) = some (toJson outcome) ∨
    ∃ result, CompletedAt journal parent.key result

theorem ChildReported.grow {before after parent index outcome}
    (recorded : ChildReported before parent index outcome) (growth : Extends before after) :
    ChildReported after parent index outcome := by
  rcases recorded with slot | ⟨result, completed⟩
  · exact .inl (growth _ _ slot)
  · exact .inr ⟨result, completed.grow growth⟩

/-- A branch is represented by a recoverable work item, has already reported
its result, is waiting on represented children, or has advanced through a
completed fork to a represented continuation. `done` is its parent's durable
slot, or the durable final outcome for the root. -/
inductive Coverage (journal : Journal) (pending : Location → Prop) :
    ExecutionTree → Location → Prop → Prop where
  | reported {tree current done} (recorded : done) : Coverage journal pending tree current done
  | queued {tree current done source} (available : pending source)
      (wake : WakePath journal source current) : Coverage journal pending tree current done
  | delay {tree current done} (rest : Coverage journal pending tree current done) :
      Coverage journal pending (.delay tree) current done
  | waiting {children result next current done}
      (descriptor : journal (forkKey current.key) = some (toJson children.length))
      (uncached : journal (resultKey current.key) = none)
      (missing : ∃ index : Fin children.length, journal (childKey current.key index.val) = none)
      (represented : ∀ index : Fin children.length,
        Coverage journal pending children[index.val] (current.child index.val)
          (ChildReported journal current index.val children[index.val].exit)) :
      Coverage journal pending (.fork children result next) current done
  | continued {children result tree current done}
      (completed : CompletedAt journal current.key (encodeOutcome (inferInstance : Codec Json) result))
      (rest : Coverage journal pending tree current.next done) :
      Coverage journal pending (.fork children result (some tree)) current done

/-- Adding transport messages never invalidates existing coverage. -/
theorem Coverage.mono_work {journal before after tree current done}
    (covered : Coverage journal before tree current done) (retains : ∀ location, before location → after location) :
    Coverage journal after tree current done := by
  induction covered with
  | reported recorded => exact .reported recorded
  | queued available wake => exact .queued (retains _ available) wake
  | delay rest ih => exact .delay ih
  | waiting descriptor uncached missing represented ih => exact .waiting descriptor uncached missing ih
  | continued completed rest ih => exact .continued completed ih

/-- Journal growth retains coverage if a previously waiting group either still
has a missing slot, or has a message that can wake its join. This isolates the
worker's journal obligation: recording the last child must not strand its
parent between the slot write and successor publication. -/
theorem Coverage.grow {before after pending tree current done done'}
    (covered : Coverage before pending tree current done) (growth : Extends before after)
    (reported : done → done')
    (joins : ∀ location children result next,
      (location, ExecutionTree.fork children result next) ∈ tree.nodes current →
      before (forkKey location.key) = some (toJson children.length) →
      before (resultKey location.key) = none →
      (∃ index : Fin children.length, before (childKey location.key index.val) = none) →
      (after (resultKey location.key) = none ∧
        ∃ index : Fin children.length, after (childKey location.key index.val) = none) ∨
      ∃ source, pending source ∧ WakePath after source location) :
    Coverage after pending tree current done' := by
  induction covered generalizing done' with
  | reported recorded => exact .reported (reported recorded)
  | queued available wake => exact .queued available (wake.grow growth)
  | delay rest ih =>
    apply Coverage.delay (ih reported ?_)
    intro location children result next member
    exact joins location children result next (by simpa only [ExecutionTree.nodes] using member)
  | @waiting children result next current done descriptor uncached missing represented ih =>
    rcases joins current children result next (by unfold ExecutionTree.nodes; exact List.mem_cons_self) descriptor uncached missing with
      ⟨uncachedNow, missingNow⟩ | ⟨source, available, wake⟩
    · refine .waiting (growth _ _ descriptor) uncachedNow missingNow ?_
      intro index
      apply ih index (fun stored => stored.grow growth)
      intro location descendants outcome later member
      exact joins location descendants outcome later
        (ExecutionTree.child_nodes_subset children result next current index member)
    · exact .queued available wake
  | @continued children result tree current done completed rest ih =>
    refine .continued (completed.grow growth) (ih reported ?_)
    intro location descendants outcome later member
    exact joins location descendants outcome later (by simp [ExecutionTree.nodes, member])

/-- An initialized fork is either still waiting on a missing slot or has a
durable completion witness. A completed cache is optional. -/
theorem Expansion.fork_coverage_cases {m : Type → Type u} {program : Cloud m Json} {tree root location children result next}
    (expansion : Expansion program tree) (nonempty : 0 < root.size)
    (member : (location, ExecutionTree.fork children result next) ∈ tree.nodes root)
    (journal : Journal) (bounded : Extends journal (tree.journal root))
    (initialized : journal (forkKey location.key) = some (toJson children.length)) :
    (journal (resultKey location.key) = none ∧
      ∃ index : Fin children.length, journal (childKey location.key index.val) = none) ∨
    CompletedAt journal location.key (encodeOutcome (inferInstance : Codec Json) result) := by
  obtain ⟨_, expected, fields⟩ := tree.fork_fields nonempty member
  cases cached : journal (resultKey location.key) with
  | some value =>
    have same := (bounded _ _ cached).symm.trans expected
    cases same
    exact .inr (.cached cached)
  | none =>
    by_cases missing : ∃ index : Fin children.length, journal (childKey location.key index.val) = none
    · exact .inl ⟨rfl, missing⟩
    · right
      have recorded (index : Fin children.length) :
          journal (childKey location.key index.val) = some (toJson children[index.val].exit) := by
        cases stored : journal (childKey location.key index.val) with
        | none => exact False.elim (missing ⟨index, stored⟩)
        | some value =>
          have same := (bounded _ _ stored).symm.trans (fields index)
          cases same
          rfl
      obtain ⟨source, expanded⟩ := expansion.node member
      refine .group (ExecutionTree.slots children) (by simpa [ExecutionTree.slots] using initialized) ?_ expanded.fork_result
      intro index inside
      have bound : index < children.length := by simpa [ExecutionTree.slots] using inside
      exact ⟨children[index].exit, by simp [ExecutionTree.slots, bound], recorded ⟨index, bound⟩⟩

/-- The worker only needs to account for joins newly made readable by its
journal writes. Still-partial groups retain coverage of their children. -/
theorem Coverage.grow_of_woken {m : Type → Type u} {program : Cloud m Json}
    {tree current before after pending done done'}
    (expansion : Expansion program tree) (nonempty : 0 < current.size)
    (covered : Coverage before pending tree current done) (growth : Extends before after)
    (bounded : Extends after (tree.journal current)) (reported : done → done')
    (woken : ∀ location children result next,
      (location, ExecutionTree.fork children result next) ∈ tree.nodes current →
      before (forkKey location.key) = some (toJson children.length) →
      before (resultKey location.key) = none →
      (∃ index : Fin children.length, before (childKey location.key index.val) = none) →
      CompletedAt after location.key (encodeOutcome (inferInstance : Codec Json) result) →
      ∃ source, pending source ∧ WakePath after source location) :
    Coverage after pending tree current done' := by
  apply covered.grow growth reported
  intro location children result next member initialized uncached missing
  rcases expansion.fork_coverage_cases nonempty member after bounded (growth _ _ initialized) with waiting | completed
  · exact .inl waiting
  · exact .inr (woken location children result next member initialized uncached missing completed)

end LeanCloud.Proofs
