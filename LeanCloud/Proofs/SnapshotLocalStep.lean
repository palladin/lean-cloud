import LeanCloud.Proofs.EvaluationContinuation
import LeanCloud.Proofs.SnapshotAdvance
import LeanCloud.Proofs.SnapshotIsolation

/-! Every fresh pending computation can take an actual worker step. Delays are
transparent, and the resulting snapshot records the updated control state.
The enclosing parent may be any open group, independently of queue order. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal ReplayModel

theorem ReplayModel.Parent.Valid.next_command {owner : Parent} {journal : Journal} {parent : Location} {branch command : Nat}
    (valid : owner.Valid (commandLocation parent branch command) journal) :
    owner.Valid (commandLocation parent branch (command + 1)) journal := by
  have same : (commandLocation parent branch (command + 1)).parent? =
      (commandLocation parent branch command).parent? := by
    rw [← commandLocation_next, Location.next_parent_eq]
  cases owner <;> simpa only [Parent.Valid, same] using valid

/-- A branch either publishes more work or reports its outcome to its owner. -/
def branchResponse (owner : Parent) (status : Option (Except CloudError Json))
    (pending : List Location) : StepResult :=
  match status with
  | none => .runnable pending.toArray
  | some (.ok value) => owner.result (.success value)
  | some (.error error) => owner.result (.failure error)

/-- The enclosing group's slot changes precisely when this branch reports its
outcome. Work internal to a branch leaves its enclosing slot unfilled. -/
def ReplayModel.Parent.SlotUpdate (owner : Parent) (journal : Journal) (status : Option (Except CloudError Json)) : Prop :=
  match owner with
  | .root => True
  | .child location index slots =>
    journal location.key = some (toJson (match status with
      | none => Result.suspended slots
      | some (.ok value) => Result.settle (slots.set! index (some (.success value)))
      | some (.error error) => Result.settle (slots.set! index (some (.failure error)))))

theorem ReplayModel.Parent.slot_unchanged {owner : Parent} {journal : Journal} {location : Location}
    (valid : owner.Valid location journal) : owner.SlotUpdate journal none := by
  cases owner with
  | root => trivial
  | child _ _ _ => exact valid.2.1

theorem ReplayModel.Parent.slot_write {owner : Parent} {journal : Journal} {location : Location}
    (valid : owner.Valid location journal) (value : Json) :
    owner.SlotUpdate (journal.write location.key value) none := by
  cases owner with
  | root => trivial
  | child parent index slots =>
    exact (journal.read_write_other location.key parent.key value (Location.parent_key_ne valid.1)).trans valid.2.1

theorem ReplayModel.Parent.slot_record (owner : Parent) (journal : Journal) (location : Location) (outcome : Except CloudError Json) :
    owner.SlotUpdate (owner.record journal location (match outcome with | .ok v => .success v | .error e => .failure e))
      (some outcome) := by
  cases owner with
  | root => trivial
  | child parent index slots => cases outcome <;> exact journal.completeChild_records_parent _ _ _ _ _

def LocalAdvance (program : Cloud Id Json)
    (owner : Parent) (journal : Journal) (parent : Location) (branch command : Nat)
    (processed : Nat := 1) : Prop :=
  ∃ updated status pending bound,
    (∃ snapshot : ReplaySnapshot updated program parent branch command status pending,
      SnapshotWork snapshot processed) ∧
    journal.TouchesAt updated (commandLocation parent branch command) ∧
    journal.PreservesCompleted updated ∧ owner.SlotUpdate updated status ∧
    ∀ fuel queueItems,
      (walk db noBlobs (fuel + bound) program
        (commandLocation parent branch command) (commandLocation parent branch command)).run
          ⟨journal, queueItems, none⟩ =
        ((.ok (branchResponse owner status pending), ⟨updated, queueItems, none⟩))

private theorem fresh_parallel_advance (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud Id α)
    (continuation : ArrsF (Control Id) (Array α) Json)
    (owner : Parent) (journal : Journal) (parent : Location) (branch command : Nat) (fresh : journal.FreshBetween (commandLocation parent branch command) (parent.child (branch + 1)))
    (valid : owner.Valid (commandLocation parent branch command) journal) :
    LocalAdvance (.impure (.parallel codec count branches) continuation) owner journal parent branch command := by
  obtain ⟨snapshot, cost, executed⟩ := snapshot_parallel_start codec count branches continuation
    journal parent branch command fresh
  refine ⟨_, none, _, 1, ⟨snapshot, cost⟩, .write _ _ _,
    journal.preservesCompleted_write_missing _ _ fresh.command_missing, Parent.slot_write valid _, ?_⟩
  simpa only [branchResponse, Array.toArray_toList] using fun fuel queueItems => executed fuel queueItems

private theorem control_local_advance {request : Control Id α} (continuation : ArrsF (Control Id) α Json)
    (owner : Parent) (journal : Journal) (parent : Location) (branch command : Nat)
    {outcome work}
    {evaluation : ControlEvaluation request outcome}
    (cost : ControlWork 1 evaluation work)
    (fresh : journal.FreshBetween (commandLocation parent branch command) (parent.child (branch + 1)))
    (valid : owner.Valid (commandLocation parent branch command) journal)
    (rest : ∀ value, outcome = .ok value →
      LocalAdvance (ArrsF.apply continuation value) owner journal parent branch command) :
    LocalAdvance (.impure request continuation) owner journal parent branch command := by
  cases cost with
  | delay =>
    obtain ⟨updated, status, pending, bound, ⟨snapshot, cost⟩, touched, kept, slots, executed⟩ := rest () rfl
    refine ⟨updated, status, pending, bound + 1,
      ⟨_, .delay cost⟩, touched, kept, slots, ?_⟩
    intro fuel queueItems
    rw [← Nat.add_assoc, walk]
    exact executed fuel queueItems
  | fail error =>
    obtain ⟨snapshot, cost, executed⟩ := snapshot_failed error continuation owner journal parent branch command fresh valid
    exact ⟨_, some (.error error), [], 1, ⟨snapshot, cost⟩,
      Parent.record_touches valid _, Parent.record_preserves_missing valid _ fresh.command_missing,
      Parent.slot_record owner journal (commandLocation parent branch command) (.error error), fun fuel queueItems => executed fuel queueItems⟩
  | parallel _ => exact fresh_parallel_advance _ _ _ _ owner journal parent branch command fresh valid

private theorem fresh_advance_of_evaluation (program : Cloud Id Json) (owner : Parent)
    (journal : Journal) (parent : Location) (branch command : Nat) (supported : PureProgram program)
    (fresh : journal.FreshBetween (commandLocation parent branch command) (parent.child (branch + 1)))
    (valid : owner.Valid (commandLocation parent branch command) journal)
    {outcome work}
    {evaluation : Evaluation program outcome}
    (cost : ProgramWork 1 evaluation work) :
    LocalAdvance program owner journal parent branch command := by
  match cost with
  | .pure value =>
    obtain ⟨snapshot, cost, executed⟩ := snapshot_returned value owner journal parent branch command fresh valid
    exact ⟨_, some (.ok value), [], 1, ⟨snapshot, cost⟩,
      Parent.record_touches valid _, Parent.record_preserves_missing valid _ fresh.command_missing,
      Parent.slot_record owner journal (commandLocation parent branch command) (.ok value), fun fuel queueItems => executed fuel queueItems⟩
  | .success control rest =>
    apply control_local_advance _ owner journal parent branch command control fresh valid
    intro value same
    cases same
    obtain ⟨_, remaining⟩ := rest.apply supported.2
    exact fresh_advance_of_evaluation _ owner journal parent branch command
      (supported.2.apply _) fresh valid remaining
  | .failure continuation control =>
    apply control_local_advance continuation owner journal parent branch command control fresh valid
    intro value same
    cases same
termination_by work
decreasing_by
  simp_wf
  exact Nat.lt_add_of_pos_left control.positive

/-- Arbitrary pending programs, including chains of delayed continuations,
advance with some finite fuel in the pure fragment. -/
theorem fresh_local_work_advance (program : Cloud Id Json) (owner : Parent)
    (journal : Journal) (parent : Location) (branch command : Nat) (supported : PureProgram program)
    (fresh : journal.FreshBetween (commandLocation parent branch command) (parent.child (branch + 1)))
    (valid : owner.Valid (commandLocation parent branch command) journal) :
    LocalAdvance program owner journal parent branch command := by
  obtain ⟨_, evaluation⟩ := Evaluation.exists program supported
  obtain ⟨_, cost⟩ := evaluation.work_exists 1
  exact fresh_advance_of_evaluation program owner journal parent branch command supported fresh valid cost

/-- A fully reported parallel group takes its join step without repeating any
child effect. Failure is selected by array position, not completion order. -/
theorem join_local_work_advance (codec : Codec α) (law : CodecLaw codec)
    (count : Nat) (branches : Fin count → Cloud Id α)
    (continuation : ArrsF (Control Id) (Array α) Json)
    (owner : Parent) (journal : Journal) (parent : Location) (branch command : Nat) {statuses pending outcomes}
    (children : ChildSnapshots journal codec branches (commandLocation parent branch command) 0 statuses pending)
    {childrenWork : Nat} (childrenCost : ChildrenSnapshotWork children childrenWork)
    (completed : statuses.mapM id = some outcomes)
    (recorded : journal (commandLocation parent branch command).key = some (toJson (Result.settle (outcomeSlots codec statuses))))
    (fresh : journal.FreshBetween (commandLocation parent branch (command + 1)) (parent.child (branch + 1)))
    (valid : owner.Valid (commandLocation parent branch command) journal) :
    LocalAdvance (.impure (.parallel codec count branches) continuation) owner journal parent branch command (childrenWork + 2) := by
  obtain ⟨evaluation, evaluationCost⟩ := childrenCost.completed law completed
  rw [outcomeSlots_full codec statuses outcomes completed] at recorded
  cases collected : outcomes.mapM id with
  | ok values =>
    rw [collected] at recorded
    obtain ⟨snapshot, cost, executed⟩ := snapshot_parallel_success codec law count branches continuation
      journal parent branch command outcomes values evaluation evaluationCost collected recorded fresh
    exact ⟨journal, none, _, 1, ⟨snapshot, cost⟩,
      .refl _ _, .refl _, Parent.slot_unchanged valid, fun fuel queueItems => executed fuel queueItems⟩
  | error error =>
    rw [collected] at recorded
    obtain ⟨snapshot, cost, executed⟩ := snapshot_parallel_failure codec count branches continuation owner
      journal parent branch command outcomes error evaluation evaluationCost collected recorded valid
    exact ⟨_, some (.error error), [], 1, ⟨snapshot, cost⟩,
      Parent.record_touches valid _, Parent.record_preserves_existing valid _ recorded,
      Parent.slot_record owner journal (commandLocation parent branch command) (.error error), fun fuel queueItems => executed fuel queueItems⟩

end LeanCloud.Proofs
