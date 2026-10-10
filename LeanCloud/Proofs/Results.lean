import LeanCloud.Proofs.Parallel
import LeanCloud.Proofs.Pure
import LeanCloud.Proofs.ReplayModel

namespace LeanCloud.Proofs.Results
open Lean ReplayModel ReplayInterpreter

theorem read_completed (journal : Journal) (branch : Location) (outcome : Exit)
    (present : journal.lookup (ReplayStore.returnKey branch) =
      some ⟨ReplayStore.returnRequest, outcome⟩) :
    ((store.outcome branch).run journal) = (.ok (some outcome), journal) := by
  simp only [ReplayStore.outcome]
  erw [read_then]
  simp [present]

theorem read_compatible (journal expected : Journal) (branch : Location) (outcome : Exit)
    (consistent : Extends journal expected)
    (known : expected.lookup (ReplayStore.returnKey branch) = some ⟨ReplayStore.returnRequest, outcome⟩) :
    ((store.outcome branch).run journal) =
      (.ok ((journal.lookup (ReplayStore.returnKey branch)).map (·.outcome)), journal) := by
  cases found : journal.lookup (ReplayStore.returnKey branch) with
  | none =>
    simp only [ReplayStore.outcome]
    erw [read_then]
    simp [found]
  | some record =>
    have same := Option.some.inj ((consistent _ _ found).symm.trans known)
    subst record
    exact read_completed journal branch outcome found

theorem read_children_snapshot (journal : Journal) (location : Location) (indices : List Nat)
    (found : Nat → Option Exit)
    (reads : ∀ index ∈ indices, (store.outcome (location.child index)).run journal = (.ok (found index), journal)) :
    (Internal.readChildren store location indices).run journal = (.ok (indices.mapM found), journal) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [Internal.readChildren, bind_run, reads index (by simp)]
    cases first : found index with
    | none => simp [List.mapM_cons, first]
    | some value =>
      simp only [bind_run, ih (fun i member => reads i (by simp [member])), pure_run]
      simp [List.mapM_cons, first]
      cases rest.mapM found <;> rfl

/-- A join reads exactly the completed child records, in source order. It neither
executes a child again nor changes any global record. -/
theorem join_reads_children (journal : Journal) (location : Location) (count : Nat)
    (outcomes : Nat → Exit)
    (completed : ∀ index, index < count →
      journal.lookup (ReplayStore.returnKey (location.child index)) =
        some ⟨ReplayStore.returnRequest, outcomes index⟩) :
    ((Internal.tryJoin store location count).run journal) =
      (.ok (some (collect ((Array.range count).map outcomes))), journal) := by
  simp only [Internal.tryJoin, bind_run]
  rw [read_children_snapshot journal location (List.range count) (some ∘ outcomes) (by
    intro index member
    exact read_completed journal _ _ (completed index (List.mem_range.mp member)))]
  have all : (List.range count).mapM (some ∘ outcomes) = some ((List.range count).map outcomes) :=
    List.mapM_pure
  have ordered : ((List.range count).map outcomes).toArray = (Array.range count).map outcomes := by
    apply Array.toList_inj.mp
    simp
  simp [all, ordered]

end LeanCloud.Proofs.Results
