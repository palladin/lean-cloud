import LeanCloud.Proofs.ScheduledExecution

/-! Connect arbitrary queue histories to the public replay driver. Queue polls
and acknowledgements below are observations of the supplied queue operations;
they do not assume that the queue manufactures correct program histories. -/

namespace LeanCloud.Proofs
open Lean ReplayModel ReplayInterpreter.Internal

inductive DriverExecution (queue : LeanCloud.WorkQueue State Id)
    (root : Cloud Id Json) : State → Exit → State → Prop where
  | completed {state exit}
      (recorded : state.completed = some exit)
      (polled : queue.next state = ((Work.completed exit, state))) :
      DriverExecution queue root state exit state
  | idle {state exit finalState}
      (polled : queue.next state = ((Work.idle, state)))
      (rest : DriverExecution queue root state exit finalState) :
      DriverExecution queue root state exit finalState
  | more {journal updated pending target locations bound exit finalState}
      (selected : target ∈ pending)
      (polled : queue.next ⟨journal, pending, none⟩ = ((Work.item target, ⟨journal, pending, none⟩)))
      (stepped : ∀ fuel,
        (step db noBlobs (fuel + bound) root target).run ⟨journal, pending, none⟩ =
          ((.ok (.runnable locations), ⟨updated, pending, none⟩)))
      (published : queue.complete target (.runnable locations) ⟨updated, pending, none⟩ =
        (((), update ⟨updated, pending, none⟩ target (.runnable locations))))
      (rest : DriverExecution queue root (update ⟨updated, pending, none⟩ target (.runnable locations))
         exit finalState) :
      DriverExecution queue root ⟨journal, pending, none⟩ exit finalState
  | finish {journal updated pending target exit bound}
      (selected : target ∈ pending)
      (polled : queue.next ⟨journal, pending, none⟩ = ((Work.item target, ⟨journal, pending, none⟩)))
      (stepped : ∀ fuel,
        (step db noBlobs (fuel + bound) root target).run ⟨journal, pending, none⟩ =
          ((.ok (.done exit), ⟨updated, pending, none⟩)))
      (published : queue.complete target (.done exit) ⟨updated, pending, none⟩ =
        (((), update ⟨updated, pending, none⟩ target (.done exit)))) :
      DriverExecution queue root ⟨journal, pending, none⟩ exit
        (update ⟨updated, pending, none⟩ target (.done exit))

theorem DriverExecution.completed_snapshot {queue : LeanCloud.WorkQueue State Id}
    {root : Cloud Id Json} {state exit finalState}
    (execution : DriverExecution queue root state exit finalState)
    (supported : PureProgram root) (snapshot : RootSnapshot root state) :
    RootSnapshot root finalState ∧ finalState.completed = some exit := by
  induction execution with
  | completed recorded _ => exact ⟨snapshot, recorded⟩
  | idle _ _ ih => exact ih snapshot
  | more selected _ stepped _ _ ih =>
    exact ih (snapshot.worker_step supported (.process _ _ _ _ _ _ selected stepped))
  | finish selected _ stepped _ =>
    exact ⟨snapshot.worker_step supported (.process _ _ _ _ _ _ selected stepped), rfl⟩

private theorem lift_observation {action : StateT State Id α} {state value nextState}
    (observed : action state = ((value, nextState))) :
    (liftM action : ExceptT CloudError (StateT State Id) α).run state =
      ((.ok value, nextState)) := by
  change (let (value, state') := action state ; ((Except.ok value, state'))) = _
  rw [observed]

private theorem run_idle [Codec α] (queue : LeanCloud.WorkQueue State Id)
    (root : Cloud Id Json) (fuel : Nat) (state : State) (polled : queue.next state = ((Work.idle, state))) :
    (run (α := α) db noBlobs queue (fuel + 1) root).run state =
      (run (α := α) db noBlobs queue fuel root).run state := by
  rw [run, run_bind, lift_observation polled]

private theorem run_completed [Codec α] (queue : LeanCloud.WorkQueue State Id)
    (root : Cloud Id Json) (fuel : Nat) (state : State) (exit : Exit)
    (polled : queue.next state = ((Work.completed exit, state))) :
    (run (α := α) db noBlobs queue (fuel + 1) root).run state =
      ((decodeExit exit, state)) := by
  rw [run, run_bind, lift_observation polled]
  exact result_run exit state

private theorem run_item [Codec α] (queue : LeanCloud.WorkQueue State Id)
    (root : Cloud Id Json) (fuel : Nat) (state : State) (target : Location) (response : StepResult) (nextState : State) (after : State)
    (polled : queue.next state = ((Work.item target, state)))
    (stepped : (step db noBlobs (fuel + 1) root target).run state = ((.ok response, nextState)))
    (published : queue.complete target response nextState = (((), after))) :
    (run (α := α) db noBlobs queue (fuel + 1) root).run state =
      match response with
      | .runnable _ => (run (α := α) db noBlobs queue fuel root).run after
      | .done exit => ((decodeExit exit, after)) := by
  rw [run]
  simp only [run_bind, lift_observation polled, stepped, lift_observation published]
  cases response with
  | runnable _ => rfl
  | done exit => exact result_run exit after

/-- Every finite, realized queue history has a sufficient fuel budget for the
actual driver. Extra fuel does not change its output or its final state. -/
theorem DriverExecution.correct [Codec α] {queue : LeanCloud.WorkQueue State Id} {root : Cloud Id Json}
    {state exit finalState}
    (execution : DriverExecution queue root state exit finalState) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      (run (α := α) db noBlobs queue fuel root).run state =
        ((decodeExit exit, finalState)) := by
  induction execution with
  | completed recorded polled =>
    refine ⟨1, ?_⟩
    intro fuel enough
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    exact run_completed queue root fuel _ _ polled
  | idle polled rest ih =>
    obtain ⟨bound, correct⟩ := ih
    refine ⟨bound + 1, ?_⟩
    intro fuel enough
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    exact (run_idle queue root fuel _ polled).trans (correct fuel (by omega))
  | @more journal updated pending target locations stepBound exit finalState
      selected polled stepped published rest ih =>
    obtain ⟨bound, correct⟩ := ih
    refine ⟨max stepBound (bound + 1), ?_⟩
    intro fuel enough
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    have stepRun := stepped (fuel + 1 - stepBound)
    have budget : fuel + 1 - stepBound + stepBound = fuel + 1 := by omega
    rw [budget] at stepRun
    exact (run_item queue root fuel _ target (.runnable locations) _ _ polled stepRun published).trans
      (correct fuel (by omega))
  | @finish journal updated pending target exit stepBound selected polled stepped published =>
    refine ⟨max stepBound 1, ?_⟩
    intro fuel enough
    obtain ⟨fuel, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    have stepRun := stepped (fuel + 1 - stepBound)
    have budget : fuel + 1 - stepBound + stepBound = fuel + 1 := by omega
    rw [budget] at stepRun
    exact run_item queue root fuel _ target (.done exit) _ _ polled stepRun published

/-- The public replay interpreter agrees with the direct interpreter for any
completed valid queue execution of a pure workflow. -/
theorem arbitrary_queue_same_output [codec : Codec α]
    (queue : LeanCloud.WorkQueue State Id) (program : ι → Cloud Id α)
    (input : ι) (law : CodecLaw codec) (supported : PureProgram (program input))
    {exit finalState}
    (execution : DriverExecution queue (codec.encode <$> program input)
      ⟨Journal.empty, [Location.root], none⟩ exit finalState) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      ((LeanCloud.interpret db noBlobs queue fuel program input).run initial).1 = direct (program input) := by
  obtain ⟨bound, correct⟩ := execution.correct (α := α)
  refine ⟨bound, ?_⟩
  intro fuel enough
  unfold LeanCloud.interpret initial
  rw [correct fuel enough]
  obtain ⟨snapshot, completed⟩ := execution.completed_snapshot (supported.map codec.encode) (.initial _)
  exact snapshot.same_output program input law completed

end LeanCloud.Proofs
