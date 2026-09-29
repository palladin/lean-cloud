import LeanCloud.Proofs.CoverageReplacement

/-! Structural progress after the immutable journal stops changing. A delivered
command either reports its branch, exposes missing children, or advances to its
continuation. This is proof data about responses, not a second interpreter. -/

namespace LeanCloud.Proofs
open Lean JournalDb JournalAdapter ReplayRecovery

/-- A stable command's response only exposes structurally smaller work. Initial
fork publication is absent: it necessarily adds a previously missing record. -/
inductive StableAdvance (journal : Journal) (available : Location → Prop) :
    ExecutionTree → Location → Prop → Prop where
  | reported {tree current done} (recorded : done) : StableAdvance journal available tree current done
  | waiting {children result next current done}
      (descriptor : journal (forkKey current.key) = some (toJson children.length))
      (uncached : journal (resultKey current.key) = none)
      (missing : ∃ index : Fin children.length, journal (childKey current.key index.val) = none)
      (childrenReady : ∀ index : Fin children.length,
        ChildReported journal current index.val children[index.val].exit ∨ available (current.child index.val)) :
      StableAdvance journal available (.fork children result next) current done
  | continued {children result next current done}
      (completed : CompletedAt journal current.key (encodeOutcome (inferInstance : Codec Json) result))
      (ready : available current.next) :
      StableAdvance journal available (.fork children result (some next)) current done

/-- Actual obsolete responses publish the parent. Closing a set of delivered
locations under those responses also closes it under every finite wake path. -/
theorem WakePath.available {journal source target} {available : Location → Prop}
    (wake : WakePath journal source target) (ready : available source)
    (parents : ∀ (source parent : Location) index outcome, source.parent? = some (parent, index) →
      CompletedAt journal parent.key outcome → available source → available parent) : available target := by
  induction wake with
  | here => exact ready
  | parent linked completed rest ih => exact ih (parents _ _ _ _ linked completed ready)

/-- A fixed journal cannot keep a delivered branch unfinished when all work
exposed by its responses is also eventually delivered. Only finite program
structure is used; the transport may contain arbitrarily many duplicates. -/
theorem ExecutionTree.stable_delivered {top : ExecutionTree} {journal available rootDone root}
    (tree : ExecutionTree) (current : Location) (nonempty : 0 < current.size)
    (embedded : tree.nodes current ⊆ top.nodes root)
    (responses : ∀ location node, (location, node) ∈ top.nodes root → available location →
      StableAdvance journal available node location (BranchReported journal rootDone node location))
    (ready : available current) : BranchReported journal rootDone tree current := by
  cases tree with
  | terminal outcome =>
    have advanced := responses current (.terminal outcome) (embedded (by simp [ExecutionTree.nodes])) ready
    cases advanced with
    | reported done => exact done
  | delay rest =>
    exact ExecutionTree.stable_delivered rest current nonempty
      (by simpa only [ExecutionTree.nodes] using embedded) responses ready
  | fork children result next =>
    have advanced := responses current (.fork children result next)
      (embedded (by unfold ExecutionTree.nodes; exact List.mem_cons_self)) ready
    cases advanced with
    | reported done => exact done
    | waiting descriptor uncached missing childrenReady =>
      obtain ⟨index, absent⟩ := missing
      have reported : ChildReported journal current index.val children[index.val].exit := by
        rcases childrenReady index with reported | childReady
        · exact reported
        · have child := ExecutionTree.stable_delivered children[index.val] (current.child index.val) (by simp)
            ((ExecutionTree.child_nodes_subset children result next current index).trans embedded) responses childReady
          simpa only [BranchReported, Location.parent_child current nonempty] using child
      rcases reported with recorded | ⟨outcome, completed⟩
      · simp [absent] at recorded
      · exact False.elim (completed.no_missing uncached descriptor index absent)
    | @continued _ _ next _ _ completed nextReady =>
      have later := ExecutionTree.stable_delivered next current.next (by simpa using nonempty)
        (fun _ member => embedded (by simp [ExecutionTree.nodes, member])) responses nextReady
      simpa only [BranchReported, Location.next_parent_eq, ExecutionTree.exit, ExecutionTree.outcome] using later
termination_by sizeOf tree
decreasing_by
  all_goals simp_wf
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  have smaller := List.sizeOf_lt_of_mem (List.getElem_mem index.isLt)
  omega

/-- Coverage and eventual delivery force completion once every delivered
response has the stable structural form above. Fair delivery and the actual
worker must supply the two closure hypotheses; completion is not one of them. -/
theorem Coverage.stable_complete {top tree : ExecutionTree} {journal available rootDone root current done}
    (covered : Coverage journal available tree current done)
    (nonempty : 0 < current.size) (embedded : tree.nodes current ⊆ top.nodes root)
    (reported : done = BranchReported journal rootDone tree current)
    (responses : ∀ location node, (location, node) ∈ top.nodes root → available location →
      StableAdvance journal available node location (BranchReported journal rootDone node location))
    (parents : ∀ source parent index outcome, source.parent? = some (parent, index) →
      CompletedAt journal parent.key outcome → available source → available parent) : done := by
  induction covered with
  | reported recorded => exact recorded
  | @queued tree current done source ready wake =>
    rw [reported]
    exact ExecutionTree.stable_delivered tree current nonempty embedded responses (wake.available ready parents)
  | delay rest ih => exact ih nonempty (by simpa only [ExecutionTree.nodes] using embedded) reported
  | @waiting children result next current done descriptor uncached missing represented ih =>
    obtain ⟨index, absent⟩ := missing
    have child := ih index (by simp)
      ((ExecutionTree.child_nodes_subset children result next current index).trans embedded)
      (by simp only [BranchReported, Location.parent_child current nonempty])
    rcases child with recorded | ⟨outcome, completed⟩
    · simp [absent] at recorded
    · exact False.elim (completed.no_missing uncached descriptor index absent)
  | continued completed rest ih =>
    exact ih (by simpa using nonempty)
      (fun _ member => embedded (by simp [ExecutionTree.nodes, member]))
      (by simpa only [BranchReported, Location.next_parent_eq, ExecutionTree.exit, ExecutionTree.outcome] using reported)

end LeanCloud.Proofs
