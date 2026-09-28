import LeanCloud.Proofs.ReplayStep
import LeanCloud.Proofs.Freshness
import LeanCloud.Proofs.ParallelSlots

namespace LeanCloud.Proofs.ReplayModel
open Lean ReplayInterpreter.Internal

inductive Parent where
  | root
  | child (location : Location) (index : Nat) (children : Array (Option Exit))

def Parent.Valid : Parent → Location → Journal → Prop
  | .root, current, _ => current.parent? = none
  | .child parent index children, current, journal =>
      current.parent? = some (parent, index) ∧
      journal parent.key = some (toJson (Result.suspended children)) ∧
      index < children.size ∧ children[index]! = none

def Parent.record (parent : Parent) (journal : Journal) (current : Location) (outcome : Exit) : Journal :=
  match parent with
  | .root => journal.write current.key (toJson (Result.completed outcome))
  | .child parent index children => journal.completeChild current parent children index outcome

def Parent.result (parent : Parent) (outcome : Exit) : StepResult :=
  match parent with
  | .root => .done outcome
  | .child parent index children =>
    match Result.settle (children.set! index (some outcome)) with
    | .suspended _ => .runnable #[]
    | .completed _ => .runnable #[parent]

theorem Parent.Valid.openParent {parent : Parent} {current : Location} {journal : Journal}
    (valid : parent.Valid current journal) : ParentOpen journal current := by
  intro location index linked
  cases parent with
  | root =>
    change current.parent? = none at valid
    rw [valid] at linked
    cases linked
  | child other otherIndex children =>
    have equal := valid.1.symm.trans linked
    cases equal
    exact ⟨children, valid.2.1⟩

theorem failure_bne_self (error : CloudError) : (Exit.failure error != Exit.failure error) = false := by
  rcases error with ⟨kind, message⟩
  cases kind <;>
    simp [bne, BEq.beq, instBEqExit.beq, instBEqCloudError.beq, instBEqErrorKind.beq]

/-- Completion only needs its own record to be absent and its parent slot open.
Other branches may already have written later locations in the journal. -/
theorem finish_missing (parent : Parent) (location : Location) (outcome : Exit)
    (journal : Journal) (pending : List Location) (missing : journal location.key = none)
    (valid : parent.Valid location journal) :
    (finish db location outcome).run ⟨journal, pending, none⟩ =
      ((.ok (parent.result outcome), ⟨parent.record journal location outcome, pending, none⟩)) := by
  cases parent with
  | root =>
    change location.parent? = none at valid
    exact finish_fresh_root _ _ _ missing valid
  | child parent index children =>
    obtain ⟨linked, parentRecorded, inside, missingSlot⟩ := valid
    have parentKept : (journal.write location.key (toJson (Result.completed outcome))) parent.key =
        some (toJson (Result.suspended children)) := by
      rw [Journal.read_write_other _ _ _ _ (Location.parent_key_ne linked), parentRecorded]
    rw [finish]
    simp only [run_bind, load_missing ⟨journal, pending, none⟩ location missing,
      save_result, linked, load_recorded ⟨journal.write location.key (toJson (Result.completed outcome)), pending, none⟩ parent _ parentKept,
      Result.recordChild_missing children index outcome inside missingSlot, run_pure,
      Parent.record, Parent.result, Journal.completeChild]
    cases settled : Result.settle (children.set! index (some outcome)) <;> rfl

theorem finish_existing_failure (parent : Parent) (location : Location) (error : CloudError)
    (journal : Journal) (pending : List Location) (recorded : journal location.key = some (toJson (Result.completed (.failure error))))
    (valid : parent.Valid location journal) :
    (finish db location (.failure error)).run ⟨journal, pending, none⟩ =
      ((.ok (parent.result (.failure error)),
        ⟨parent.record journal location (.failure error), pending, none⟩)) := by
  cases parent with
  | root =>
    change location.parent? = none at valid
    rw [finish]
    simp only [run_bind, load_recorded ⟨journal, pending, none⟩ location _ recorded,
      failure_bne_self, Bool.false_eq_true, ↓reduceIte, run_pure, valid,
      Parent.record, Parent.result, journal.write_existing _ _ recorded]
  | child parent index children =>
    obtain ⟨linked, parentRecorded, inside, missingSlot⟩ := valid
    rw [finish]
    simp only [run_bind, load_recorded ⟨journal, pending, none⟩ location _ recorded,
      failure_bne_self, Bool.false_eq_true, ↓reduceIte, run_pure, linked,
      load_recorded ⟨journal, pending, none⟩ parent _ parentRecorded,
      Result.recordChild_missing children index _ inside missingSlot, save_result,
      Parent.record, Parent.result, Journal.completeChild, journal.write_existing _ _ recorded]
    cases settled : Result.settle (children.set! index (some (.failure error))) <;> rfl

theorem Parent.records_current {parent : Parent} {journal : Journal} {location : Location}
    (valid : parent.Valid location journal) (outcome : Exit) :
    parent.record journal location outcome location.key = some (toJson (Result.completed outcome)) := by
  cases parent with
  | root => exact journal.read_write _ _
  | child parent index children =>
    exact journal.completeChild_records_child location parent children index outcome valid.1

theorem walk_recorded_parallel_failure (fuel : Nat)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud Id α)
    (continuation : LeanEff.ArrsF (Control Id) (Array α) Json) (error : CloudError)
    (current : Location) (state : State) (recorded : state.journal current.key = some (toJson (Result.completed (.failure error)))) :
    (walk db noBlobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current current).run state =
      (finish db current (.failure error)).run state := by
  rw [walk]
  simp only [run_bind, load_recorded state current _ recorded, beq_self_eq_true,
    Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

end LeanCloud.Proofs.ReplayModel
