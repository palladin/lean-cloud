import LeanCloud.Proofs.ReplaySegment
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

def Parent.after (parent : Parent) (journal : Journal) (current : Location)
    (outcome : Exit) (rest : List Location) : State :=
  update ⟨parent.record journal current outcome, current :: rest, none⟩ current (parent.result outcome)

theorem Parent.Valid.openParent {parent : Parent} {current : Location} {journal : Journal}
    (valid : parent.Valid current journal) : ReplayRoute.ParentOpen journal current := by
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

theorem Parent.Valid.preserve {parent : Parent} {current next : Location} {journal updated : Journal}
    (valid : parent.Valid current journal) (sameParent : next.parent? = current.parent?)
    (ancestors : journal.PreservesAncestors updated current) : parent.Valid next updated := by
  cases parent with
  | root => exact sameParent.trans valid
  | child parent index children =>
    have sizes := Location.parent_size valid.1
    exact ⟨sameParent.trans valid.1, (ancestors parent sizes.1 (by omega)).trans valid.2.1,
      valid.2.2⟩

/-- A fresh completion or a failure already recorded by a nested group. -/
inductive ReturnReady (journal : Journal) (location : Location) : Exit → Prop where
  | fresh {outcome} (available : journal.Fresh location) : ReturnReady journal location outcome
  | failure (error : CloudError)
      (recorded : journal location.key = some (toJson (Result.completed (.failure error))))
      (available : journal.Fresh location.next) : ReturnReady journal location (.failure error)

theorem failure_bne_self (error : CloudError) : (Exit.failure error != Exit.failure error) = false := by
  rcases error with ⟨kind, message⟩
  cases kind <;>
    simp [bne, BEq.beq, instBEqExit.beq, instBEqCloudError.beq, instBEqErrorKind.beq]

theorem finish_ready (blobs : BlobModel World) (parent : Parent) (location : Location) (outcome : Exit)
    (journal : Journal) (pending : List Location) (world : World)
    (nonempty : 0 < location.size) (ready : ReturnReady journal location outcome)
    (valid : parent.Valid location journal) :
    (finish (storage blobs) location outcome).run ⟨journal, pending, none⟩ world =
      ((.ok (parent.result outcome), ⟨parent.record journal location outcome, pending, none⟩), world) := by
  cases parent with
  | root =>
    change location.parent? = none at valid
    cases ready with
    | fresh available =>
      exact finish_fresh_root blobs _ _ _ _ (available.missing nonempty) valid
    | failure error recorded available =>
      rw [finish]
      simp only [run_bind, load_recorded blobs ⟨journal, pending, none⟩ world location _ recorded,
        failure_bne_self, Bool.false_eq_true, ↓reduceIte, run_pure, valid,
        Parent.record, Parent.result, journal.write_existing _ _ recorded]
  | child parent index children =>
    obtain ⟨linked, parentRecorded, inside, missingSlot⟩ := valid
    cases ready with
    | fresh available =>
      have parentKept : (journal.write location.key (toJson (Result.completed outcome))) parent.key =
          some (toJson (Result.suspended children)) := by
        rw [Journal.read_write_other _ _ _ _ (Location.parent_key_ne linked), parentRecorded]
      rw [finish]
      simp only [run_bind, load_missing blobs ⟨journal, pending, none⟩ world location (available.missing nonempty),
        save_result, linked, load_recorded blobs
          ⟨journal.write location.key (toJson (Result.completed outcome)), pending, none⟩ world parent _ parentKept,
        Result.recordChild_missing children index outcome inside missingSlot, run_pure,
        Parent.record, Parent.result, Journal.completeChild]
      cases settled : Result.settle (children.set! index (some outcome)) <;> rfl
    | failure error recorded available =>
      rw [finish]
      simp only [run_bind, load_recorded blobs ⟨journal, pending, none⟩ world location _ recorded,
        failure_bne_self, Bool.false_eq_true, ↓reduceIte, run_pure, linked,
        load_recorded blobs ⟨journal, pending, none⟩ world parent _ parentRecorded,
        Result.recordChild_missing children index _ inside missingSlot, save_result,
        Parent.record, Parent.result, Journal.completeChild, journal.write_existing _ _ recorded]
      cases settled : Result.settle (children.set! index (some (.failure error))) <;> rfl

/-- A proved local completion gives a segment of the actual root-based driver. -/
theorem report_segment (blobs : BlobModel World) (root program : Cloud (StateM World) Json)
    (parent : Parent) (location : Location) (outcome : Exit) (journal : Journal)
    (world : World) (rest : List Location) (steps : Nat)
    (route : ReplayRoute journal root Location.root program location steps)
    (ready : ReturnReady journal location outcome) (valid : parent.Valid location journal)
    (terminal : ∀ fuel,
      (walk (storage blobs) (fuel + 1) program location location).run ⟨journal, location :: rest, none⟩ world =
        (finish (storage blobs) location outcome).run ⟨journal, location :: rest, none⟩ world) :
    Segment blobs root ⟨journal, location :: rest, none⟩ world
      (parent.after journal location outcome rest) world := by
  apply Segment.one (bound := steps + 1)
  intro fuel enough
  have nonempty : 0 < location.size := by have := route.depth_le; simp only [Location.size_root] at this; omega
  have budget : fuel = (fuel - steps - 1 + 1) + steps := by omega
  rw [budget, route.from_root valid.openParent, terminal]
  exact finish_ready blobs parent location outcome journal _ world nonempty ready valid

theorem walk_fresh_sequential_failure (blobs : BlobModel World) (fuel : Nat)
    (codec : Codec α) (operation : Operation (StateM World) α)
    (continuation : LeanEff.ArrsF (Control (StateM World)) α Json) (error : CloudError)
    (current : Location) (state : State) (world nextWorld : World)
    (missing : state.journal current.key = none)
    (executed : ((storage blobs).execute operation).run state world = ((.error error, state), nextWorld)) :
    (walk (storage blobs) (fuel + 1) (.impure (.sequential codec operation) continuation) current current).run state world =
      (finish (storage blobs) current (.failure error)).run state nextWorld := by
  let saved : State := { state with journal := state.journal.write current.key (toJson (Result.completed (.failure error))) }
  have recorded : saved.journal current.key = some (toJson (Result.completed (.failure error))) :=
    state.journal.read_write _ _
  rw [walk]
  simp only [run_bind, load_missing blobs state world current missing, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, run_catch, executed, run_pure, save_result, beq_self_eq_true]
  change (finish (storage blobs) current (.failure error)).run saved nextWorld = _
  conv => lhs; rw [finish]
  conv => rhs; rw [finish]
  simp only [run_bind, load_recorded blobs saved nextWorld current _ recorded, failure_bne_self,
    Bool.false_eq_true, ↓reduceIte, load_missing blobs state nextWorld current missing, save_result]
  rfl

theorem walk_recorded_parallel_failure (blobs : BlobModel World) (fuel : Nat)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud (StateM World) α)
    (continuation : LeanEff.ArrsF (Control (StateM World)) (Array α) Json) (error : CloudError)
    (current : Location) (state : State) (world : World)
    (recorded : state.journal current.key = some (toJson (Result.completed (.failure error)))) :
    (walk (storage blobs) (fuel + 1) (.impure (.parallel codec count branches) continuation) current current).run state world =
      (finish (storage blobs) current (.failure error)).run state world := by
  rw [walk]
  simp only [run_bind, load_recorded blobs state world current _ recorded, beq_self_eq_true,
    Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem ReturnReady.preserves_completed {parent : Parent} {journal : Journal} {location : Location} {outcome : Exit}
    (ready : ReturnReady journal location outcome) (valid : parent.Valid location journal)
    (nonempty : 0 < location.size) : journal.PreservesCompleted (parent.record journal location outcome) := by
  cases parent with
  | root =>
    cases ready with
    | fresh available => exact journal.preservesCompleted_write_missing _ _ (available.missing nonempty)
    | failure error recorded available =>
      rw [Parent.record, journal.write_existing _ _ recorded]
      exact .refl _
  | child parent index children =>
    cases ready with
    | fresh available => exact journal.completeChild_preserves _ _ _ _ _ valid.1 (available.missing nonempty) valid.2.1
    | failure error recorded available => exact journal.completeChild_preserves_existing _ _ _ _ _ recorded valid.2.1

theorem ReturnReady.fresh_next {journal : Journal} {location : Location} {outcome : Exit}
    (ready : ReturnReady journal location outcome) (nonempty : 0 < location.size) :
    journal.Fresh location.next := by
  cases ready with
  | fresh available => exact available.advance (Location.earlier_next location nonempty)
  | failure _ _ available => exact available

theorem ReturnReady.fresh_sibling {journal : Journal} {location parent : Location} {index : Nat} {outcome : Exit}
    (ready : ReturnReady journal location outcome) (linked : location.parent? = some (parent, index))
    (children : Array (Option Exit)) :
    (journal.completeChild location parent children index outcome).Fresh (parent.child (index + 1)) := by
  have depth := Location.parent_size linked
  exact (ready.fresh_next (by omega)).complete_child linked
    (Location.earlier_next_sibling (Location.next_parent linked)) children outcome

theorem ReturnReady.fresh_parent_next {journal : Journal} {location parent : Location} {index : Nat} {outcome : Exit}
    (ready : ReturnReady journal location outcome) (linked : location.parent? = some (parent, index))
    (children : Array (Option Exit)) :
    (journal.completeChild location parent children index outcome).Fresh parent.next := by
  have depth := Location.parent_size linked
  exact (ready.fresh_next (by omega)).complete_child linked
    (Location.earlier_parent_next (Location.next_parent linked)) children outcome

end LeanCloud.Proofs.ReplayModel
