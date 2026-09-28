import LeanCloud.Proofs.SnapshotWorkBound
import LeanCloud.Proofs.ScheduledExecution

/-! Lift exact processed-work accounting to actual worker calls. The bound is
derived from a direct evaluation, not supplied as a queue/backend obligation. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayModel ReplayInterpreter.Internal

theorem RootWorkSnapshot.bounded {root : Cloud Id Json} {state spent outcome total}
    {evaluation : Evaluation root outcome} (totalCost : ProgramWork 0 evaluation total)
    (snapshot : RootWorkSnapshot root state spent) (supported : PureProgram root) :
    spent + unfinishedWork state.completed ≤ total + returnWork outcome := by
  obtain ⟨status, pending, ⟨source, cost⟩, _, completed⟩ := snapshot
  have bound := cost.bounded totalCost supported
  rw [completed]
  cases status <;> exact bound

theorem RootSnapshot.unfinished_pending {root : Cloud Id Json}
    {state}
    (snapshot : RootSnapshot root state) (unfinished : state.completed = none) :
    ∃ target, target ∈ state.pending := by
  obtain ⟨status, pending, source, queued, completed⟩ := snapshot
  have absent : status = none := by
    cases status with
    | none => rfl
    | some value => simp [unfinished] at completed
  obtain ⟨target, member⟩ := source.pending_exists absent
  exact ⟨target, queued.mem_iff.mp member⟩

/-- Processing one selected item cannot discard another pending item. -/
theorem RootSnapshot.retains_unselected {root : Cloud Id Json}
    {journal updated pending target response bound other}
    (snapshot : RootSnapshot root ⟨journal, pending, none⟩)
    (supported : PureProgram root) (selected : target ∈ pending)
    (executed : ∀ fuel,
      (step db noBlobs (fuel + bound) root target).run ⟨journal, pending, none⟩ =
        ((.ok response, ⟨updated, pending, none⟩)))
    (member : other ∈ pending) (different : other ≠ target) :
    other ∈ (update ⟨updated, pending, none⟩ target response).pending := by
  cases response with
  | runnable locations =>
    exact List.mem_append_right _ ((List.mem_erase_of_ne different).mpr member)
  | done exit =>
    obtain ⟨_, structural, source, queued, _⟩ := snapshot
    obtain ⟨_, outcome, _, reply, cost, _, _, _, emission, actual⟩ :=
      source.step_preserves supported (queued.mem_iff.mpr selected)
    have same := (executed cost).symm.trans (by simpa only [Nat.add_comm] using actual bound pending)
    have replyEq := Except.ok.inj (congrArg Prod.fst same)
    subst reply
    cases outcome with
    | none => obtain ⟨_, impossible, _⟩ := emission; cases impossible
    | some value =>
      obtain ⟨_, single, _⟩ := emission
      have inside := queued.mem_iff.mpr member
      rw [single] at inside
      exact False.elim (different (List.mem_singleton.mp inside))

end LeanCloud.Proofs
