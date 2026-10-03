import LeanCloud.Proofs.BackendFinish
import LeanCloud.Proofs.ConcurrentTree

/-! The existing pure execution tree supplies formats, prescribed values and
routing facts. Only these mathematical tree facts are reused from the old proof;
service execution is governed by the common backend contracts. -/

universe u
namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanCloud.Proofs JournalDb JournalAdapter ReplayRecovery

theorem ReadResult.admitted {m : Type → Type u} {program : Cloud m Json}
    {tree node : ExecutionTree} (expansion : Expansion program tree) {root location : Location}
    (nonempty : 0 < root.size) (member : (location, node) ∈ tree.nodes root)
    {before after : Backend.State} {answer : Option Result}
    (seen : ReadResult location.key before after answer)
    (bounded : Valid (tree.journal root) after) :
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
theorem finish_tree_checked {program : Cloud Replay.M Json} {tree current node}
    (expansion : Expansion program tree) (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (initial : Backend.State) (bounded : Valid (tree.journal Location.root) initial)
    (ready : node.FinishReady current (view initial))
    (descriptors : ∀ parent index, current.parent? = some (parent, index) →
      ∃ count : Nat, view initial (forkKey parent.key) = some (toJson count)) :
    ActionChecked (tree.journal Location.root)
      (ReplayInterpreter.Internal.finish (JournalDb.ofDb Replay.rawDb) current node.exit)
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

end LeanCloud.Backend.Proofs.Journal

