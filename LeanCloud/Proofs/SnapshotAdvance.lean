import LeanCloud.Proofs.SnapshotRouting
import LeanCloud.Proofs.SnapshotWork
import LeanCloud.Proofs.ReplayCompletion
import Init.Data.Array.OfFn

/-! Initial local transitions of the real replay walk establish the corresponding
snapshot and publish its pending work. These equations do not choose a queue order. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal ReplayModel

private theorem measured_and {P Q : Prop} {cost : P → Prop}
    (measured : ∃ witness, cost witness) (rest : Q) : ∃ witness, cost witness ∧ Q := by
  obtain ⟨witness, measurement⟩ := measured
  exact ⟨witness, measurement, rest⟩

theorem ChildSnapshots.initial {journal : Journal} (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud Id α) (parent : Location) (offset : Nat)
    (fresh : ∀ index, offset ≤ index → journal.FreshBetween (parent.child index) (parent.child (index + 1))) :
    ∃ snapshot : ChildSnapshots journal codec branches parent offset (Array.replicate count none)
      (List.ofFn fun i : Fin count => parent.child (offset + i.val)), ChildrenSnapshotWork snapshot 0 := by
  induction count generalizing offset with
  | zero => exact ⟨_, .empty codec branches parent offset⟩
  | succ count ih =>
    have head := SnapshotWork.pending (codec.encode <$> branches 0) parent offset 0 (fresh offset (Nat.le_refl _))
    obtain ⟨_, tail⟩ := ih (fun index => branches index.succ) (offset + 1)
      (fun index later => fresh index (by omega))
    have combined : ∃ snapshot, ChildrenSnapshotWork (parent := parent) (offset := offset)
        (statuses := #[none] ++ Array.replicate count none) snapshot 0 := ⟨_, .cons (outcome := none) head tail⟩
    have slots : #[none] ++ (Array.replicate count none : Array (Option (Except CloudError α))) =
        Array.replicate (count + 1) none := by
      apply Array.toList_inj.mp
      simp [List.replicate_succ]
    rw [slots] at combined
    simpa only [List.ofFn_succ, Fin.val_zero, Fin.val_succ, Nat.add_zero,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.singleton_append, commandLocation,
      Location.child] using combined

/-- A fresh fork creates exactly the child snapshots and join work emitted by
the runtime, including the empty-parallel case. -/
theorem snapshot_parallel_start (codec : Codec α) (count : Nat)
    (branches : Fin count → Cloud Id α)
    (continuation : ArrsF (Control Id) (Array α) Json)
    (journal : Journal) (parent : Location) (branch command : Nat)
    (fresh : journal.FreshBetween (commandLocation parent branch command) (parent.child (branch + 1))) :
    let current := commandLocation parent branch command
    let saved := journal.write current.key (toJson (Result.settle (Array.replicate count none)))
    let published := if count == 0 then #[current] else Array.ofFn fun i : Fin count => current.child i.val
    ∃ snapshot : ReplaySnapshot saved (.impure (.parallel codec count branches) continuation) parent branch command
        none published.toList, SnapshotWork snapshot 1 ∧
      ∀ fuel queueItems,
        (walk db noBlobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current current).run
            ⟨journal, queueItems, none⟩ =
          ((.ok (.runnable published), ⟨saved, queueItems, none⟩)) := by
  dsimp only
  have nonempty : 0 < (commandLocation parent branch command).size := by simp [commandLocation]
  have missing := fresh.missing nonempty
    (Location.child_earlier_sibling parent branch command (branch + 1) (by omega))
  apply measured_and
  · obtain ⟨_, children⟩ := ChildSnapshots.initial codec count branches
      (commandLocation parent branch command) 0 (journal := journal.write
        (commandLocation parent branch command).key (toJson (Result.settle (Array.replicate count none))))
      (fun index _ => fresh.child nonempty index (by
        simpa only [commandLocation, Location.child, Array.push_eq_append] using
          Location.descendants_earlier_sibling parent branch command (branch + 1) #[(index + 1, 0)] (by omega)) _)
    have recorded : (journal.write (commandLocation parent branch command).key
        (toJson (Result.settle (Array.replicate count none)))) (commandLocation parent branch command).key =
        some (toJson (Result.settle (outcomeSlots codec (Array.replicate count none)))) := by
      simp [outcomeSlots]
    have nextFresh := fresh.next nonempty (toJson (Result.settle (Array.replicate count none)))
    rw [commandLocation_next] at nextFresh
    have forked : ∃ snapshot, SnapshotWork (program := .impure (.parallel codec count branches) continuation) snapshot 1 :=
      ⟨_, .parallel children recorded nextFresh⟩
    cases count with
    | zero => simpa [groupPending, Array.mapM_empty] using forked
    | succ count =>
      have uncollected : (Array.replicate (count + 1) (none : Option (Except CloudError α))).mapM id = none := by
        simp [Array.mapM_eq_mapM_toList, List.replicate_succ]
      simpa only [groupPending, uncollected, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        beq_iff_eq, decide_false, Bool.false_eq_true, ↓reduceIte, Array.toList_ofFn, Nat.zero_add] using forked
  · intro fuel queueItems
    exact walk_fresh_parallel fuel codec count branches continuation _ _ missing

/-- Returning a value records that value and updates the enclosing group. -/
theorem snapshot_returned (value : Json) (owner : Parent)
    (journal : Journal) (parent : Location) (branch command : Nat)
    (fresh : journal.FreshBetween (commandLocation parent branch command) (parent.child (branch + 1)))
    (valid : owner.Valid (commandLocation parent branch command) journal) :
    let current := commandLocation parent branch command
    let saved := owner.record journal current (.success value)
    ∃ snapshot : ReplaySnapshot saved (EffF.pure value) parent branch command (some (.ok value)) [], SnapshotWork snapshot 1 ∧
      ∀ fuel queueItems,
        (walk db noBlobs (fuel + 1) (EffF.pure value) current current).run
            ⟨journal, queueItems, none⟩ =
          ((.ok (owner.result (.success value)), ⟨saved, queueItems, none⟩)) := by
  dsimp only
  apply measured_and
  · exact ⟨_, .returned value (Parent.records_current valid _)⟩
  · intro fuel queueItems
    rw [walk]
    simp only [beq_self_eq_true, ↓reduceIte]
    exact finish_missing owner _ _ journal queueItems fresh.command_missing valid

theorem snapshot_failed (error : CloudError)
    (continuation : ArrsF (Control Id) α Json) (owner : Parent)
    (journal : Journal) (parent : Location) (branch command : Nat)
    (fresh : journal.FreshBetween (commandLocation parent branch command) (parent.child (branch + 1)))
    (valid : owner.Valid (commandLocation parent branch command) journal) :
    let current := commandLocation parent branch command
    let saved := owner.record journal current (.failure error)
    ∃ snapshot : ReplaySnapshot saved (.impure (.fail error) continuation) parent branch command (some (.error error)) [], SnapshotWork snapshot 1 ∧
      ∀ fuel queueItems,
        (walk db noBlobs (fuel + 1) (.impure (.fail error) continuation) current current).run
            ⟨journal, queueItems, none⟩ =
          ((.ok (owner.result (.failure error)), ⟨saved, queueItems, none⟩)) := by
  dsimp only
  apply measured_and
  · exact ⟨_, .failed error continuation (Parent.records_current valid _)⟩
  · intro fuel queueItems
    rw [walk]
    simp only [beq_self_eq_true, ↓reduceIte]
    exact finish_missing owner _ _ journal queueItems fresh.command_missing valid

/-- Joining a successful group resumes its original typed continuation without
executing any primitive effect or changing the journal. -/
theorem snapshot_parallel_success (codec : Codec α) (law : CodecLaw codec)
    (count : Nat) (branches : Fin count → Cloud Id α)
    (continuation : ArrsF (Control Id) (Array α) Json)
    (journal : Journal) (parent : Location) (branch command : Nat)
    (outcomes : Array (Except CloudError α)) (values : Array α)
    (evaluation : ChildrenEvaluation branches outcomes) {childrenWork : Nat}
    (cost : ChildrenWork 0 evaluation childrenWork) (collected : outcomes.mapM id = .ok values)
    (recorded : journal (commandLocation parent branch command).key =
      some (toJson (Result.completed (.success (Json.arr (values.map codec.encode))))))
    (fresh : journal.FreshBetween (commandLocation parent branch (command + 1)) (parent.child (branch + 1))) :
    let current := commandLocation parent branch command
    ∃ snapshot : ReplaySnapshot journal (.impure (.parallel codec count branches) continuation) parent branch command
        none [current.next], SnapshotWork snapshot (childrenWork + 2) ∧
      ∀ fuel queueItems,
        (walk db noBlobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current current).run
            ⟨journal, queueItems, none⟩ =
          ((.ok (.runnable #[current.next]), ⟨journal, queueItems, none⟩)) := by
  dsimp only
  apply measured_and
  · rw [commandLocation_next]
    have combined : ∃ snapshot, SnapshotWork (program := .impure (.parallel codec count branches) continuation) snapshot
        (childrenWork + 2 + 0) := ⟨_, .parallelSuccess cost collected recorded
          (.pending (ArrsF.apply continuation values) parent branch (command + 1) fresh)⟩
    simpa only [Nat.add_zero] using combined
  · intro fuel queueItems
    exact walk_join_parallel fuel codec law count branches continuation values _ _
      ((collect_outcomes_size _ _ collected).trans evaluation.size) recorded

/-- A failed group reports the error selected in array order, after every child
has completed. The already recorded group error is reused. -/
theorem snapshot_parallel_failure (codec : Codec α)
    (count : Nat) (branches : Fin count → Cloud Id α)
    (continuation : ArrsF (Control Id) (Array α) Json) (owner : Parent)
    (journal : Journal) (parent : Location) (branch command : Nat)
    (outcomes : Array (Except CloudError α)) (error : CloudError)
    (evaluation : ChildrenEvaluation branches outcomes) {childrenWork : Nat}
    (cost : ChildrenWork 0 evaluation childrenWork) (collected : outcomes.mapM id = .error error)
    (recorded : journal (commandLocation parent branch command).key = some (toJson (Result.completed (.failure error))))
    (valid : owner.Valid (commandLocation parent branch command) journal) :
    let current := commandLocation parent branch command
    let saved := owner.record journal current (.failure error)
    ∃ snapshot : ReplaySnapshot saved (.impure (.parallel codec count branches) continuation) parent branch command
        (some (.error error)) [], SnapshotWork snapshot (childrenWork + 2) ∧
      ∀ fuel queueItems,
        (walk db noBlobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current current).run
            ⟨journal, queueItems, none⟩ =
          ((.ok (owner.result (.failure error)), ⟨saved, queueItems, none⟩)) := by
  dsimp only
  apply measured_and
  · exact ⟨_, .parallelFailure continuation cost collected (Parent.records_current valid _)⟩
  · intro fuel queueItems
    exact (walk_recorded_parallel_failure fuel codec count branches continuation error _ _ recorded).trans
      (finish_existing_failure owner _ error journal queueItems recorded valid)

end LeanCloud.Proofs
