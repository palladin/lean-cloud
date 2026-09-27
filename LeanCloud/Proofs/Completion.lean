import LeanCloud.Proofs.ReplayInterpreter
import LeanCloud.Proofs.Parallel
import LeanCloud.Proofs.Storage

/-! Child completion in the existing replay loop. The statements below include
the exact journal writes, remaining fuel, and parent resumption. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

/-- A computation that has returned a value or explicitly failed. -/
inductive Terminal {m : Type → Type} : Cloud m Json → Exit → Prop where
  | success (value : Json) : Terminal (.pure value) (.success value)
  | failure {α : Type} (error : CloudError) (continuation : ArrsF (Control m) α Json) :
      Terminal (.impure (.fail error) continuation) (.failure error)

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

/-- A fresh terminal child writes its own outcome and then its parent's updated
result. If all slots are filled, execution restarts from the original root with
the parent as target; otherwise it returns that parent's suspension. -/
theorem walk_terminal_child {World : Type} (blobs : BlobModel World)
    (root program : Cloud (StateM World) Json) (outcome : Exit)
    (terminal : Terminal program outcome) (fuel : Nat)
    (current target parent : Location) (index : Nat)
    (journal : Journal) (world : World) (children : Array (Option Exit))
    (atFrontier : current.before target = false)
    (hasParent : current.parent? = some (parent, index))
    (missing : journal current.key = none)
    (recorded : journal parent.key = some (toJson (Result.suspended children)))
    (inside : index < children.size) (slotMissing : children[index]! = none) :
    (step.walk (modelStorage blobs) root (fuel + 1) program current target).run journal world =
      let updated := Result.settle (children.set! index (some outcome))
      let committed := journal.completeChild current parent children index outcome
      match updated with
      | .suspended _ => ((.ok (.suspended parent fuel), committed), world)
      | .completed _ =>
        (step.walk (modelStorage blobs) root fuel root Location.root parent).run committed world := by
  have parentRecorded :
      (journal.write current.key (toJson (Result.completed outcome))) parent.key =
        some (toJson (Result.suspended children)) := by
    rw [Journal.read_write_other _ _ _ _ (Location.parent_key_ne hasParent), recorded]
  cases terminal <;> rw [step.walk] <;>
    simp only [atFrontier, Bool.false_eq_true, ↓reduceIte, run_bind_state,
      load_missing blobs journal world current missing, save_result, hasParent,
      load_recorded blobs _ world parent _ parentRecorded,
      Result.recordChild_missing children index _ inside slotMissing, run_pure_state,
      Journal.completeChild]
  all_goals split <;> simp_all only [run_pure_state]

/-- A failed parallel group already has its failure recorded when completion
propagates to its parent. Its own record is retained and the parent is updated
exactly once. This uses only failure equality, not partial JSON equality. -/
theorem walk_recorded_failure_child {World α : Type} (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (error : CloudError)
    (continuation : ArrsF (Control (StateM World)) α Json) (fuel : Nat)
    (current target parent : Location) (index : Nat)
    (journal : Journal) (world : World) (children : Array (Option Exit))
    (atFrontier : current.before target = false)
    (hasParent : current.parent? = some (parent, index))
    (ownResult : journal current.key = some (toJson (Result.completed (.failure error))))
    (recorded : journal parent.key = some (toJson (Result.suspended children)))
    (inside : index < children.size) (slotMissing : children[index]! = none) :
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.fail error) continuation) current target).run journal world =
      let updated := Result.settle (children.set! index (some (.failure error)))
      let committed := journal.completeChild current parent children index (.failure error)
      match updated with
      | .suspended _ => ((.ok (.suspended parent fuel), committed), world)
      | .completed _ =>
        (step.walk (modelStorage blobs) root fuel root Location.root parent).run committed world := by
  rw [step.walk]
  simp only [atFrontier, Bool.false_eq_true, ↓reduceIte, run_bind_state,
    load_recorded blobs journal world current _ ownResult, failure_bne_self,
    run_pure_state, hasParent, load_recorded blobs journal world parent _ recorded,
    Result.recordChild_missing children index _ inside slotMissing, save_result,
    Journal.completeChild, journal.write_existing current.key _ ownResult]
  split <;> simp_all only [run_pure_state]

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
