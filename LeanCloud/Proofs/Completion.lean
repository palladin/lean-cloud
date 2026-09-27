import LeanCloud.Proofs.Codecs
import LeanCloud.Proofs.Parallel
import LeanCloud.Proofs.Storage

/-! Algebraic laws for the two journal writes made by child completion. -/

namespace LeanCloud.Proofs
open Lean

/-- The two writes made when a child finishes. This names the journal expression
in the proof statements; the runtime continues to use its existing storage calls. -/
def Journal.completeChild (journal : Journal) (current parent : Location)
    (children : Array (Option Exit)) (index : Nat) (outcome : Exit) : Journal :=
  (journal.write current.key (toJson (Result.completed outcome))).write parent.key
    (toJson (Result.settle (children.set! index (some outcome))))

/-- Both completion writes preserve the results of all previously finished work. -/
theorem Journal.completeChild_preserves (journal : Journal) (current parent : Location)
    (children : Array (Option Exit)) (index : Nat) (outcome : Exit)
    (hasParent : current.parent? = some (parent, index))
    (missing : journal current.key = none)
    (recorded : journal parent.key = some (toJson (Result.suspended children))) :
    Journal.PreservesCompleted journal (journal.completeChild current parent children index outcome) := by
  apply (Journal.preservesCompleted_write_missing journal current.key _ missing).trans
  apply Journal.preservesCompleted_write_suspended _ parent.key children
  rw [Journal.read_write_other _ _ _ _ (Location.parent_key_ne hasParent), recorded]

/-- Propagating a previously recorded outcome also preserves all completed
records: its own write is redundant and only the partial parent changes. -/
theorem Journal.completeChild_preserves_existing (journal : Journal) (current parent : Location)
    (children : Array (Option Exit)) (index : Nat) (outcome : Exit)
    (ownResult : journal current.key = some (toJson (Result.completed outcome)))
    (recorded : journal parent.key = some (toJson (Result.suspended children))) :
    Journal.PreservesCompleted journal (journal.completeChild current parent children index outcome) := by
  rw [completeChild, journal.write_existing current.key _ ownResult]
  exact journal.preservesCompleted_write_suspended parent.key children _ recorded

theorem Journal.completeChild_records_child (journal : Journal) (current parent : Location)
    (children : Array (Option Exit)) (index : Nat) (outcome : Exit)
    (hasParent : current.parent? = some (parent, index)) :
    journal.completeChild current parent children index outcome current.key =
      some (toJson (Result.completed outcome)) := by
  rw [completeChild, read_write_other _ _ _ _ (Ne.symm (Location.parent_key_ne hasParent)), read_write]

theorem Journal.completeChild_records_parent (journal : Journal) (current parent : Location)
    (children : Array (Option Exit)) (index : Nat) (outcome : Exit) :
    journal.completeChild current parent children index outcome parent.key =
      some (toJson (Result.settle (children.set! index (some outcome)))) := by
  exact read_write _ _ _

/-- Only the child's terminal location and its parent group are overwritten. -/
theorem Journal.completeChild_other (journal : Journal) (current parent : Location)
    (children : Array (Option Exit)) (index : Nat) (outcome : Exit) (key : String)
    (notChild : key ≠ current.key) (notParent : key ≠ parent.key) :
    journal.completeChild current parent children index outcome key = journal key := by
  simp only [completeChild, read_write_other _ _ _ _ notParent,
    read_write_other _ _ _ _ notChild]

/-- The child's two writes preserve every record above its parent. -/
theorem Journal.completeChild_preserves_ancestors (journal : Journal)
    (current parent : Location) (children : Array (Option Exit)) (index : Nat) (outcome : Exit)
    (hasParent : current.parent? = some (parent, index)) :
    journal.PreservesAncestors (journal.completeChild current parent children index outcome) parent := by
  obtain ⟨parentNonempty, depth⟩ := Location.parent_size hasParent
  exact (journal.write_preserves_shallower current parent _ (by omega) (by omega)).trans
    ((journal.write current.key (toJson (Result.completed outcome))).write_preserves_shallower
      parent parent _ parentNonempty (by omega))

end LeanCloud.Proofs
