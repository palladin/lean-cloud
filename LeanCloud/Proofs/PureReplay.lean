import LeanCloud.Proofs.ScheduledWork
import LeanCloud.Proofs.ScheduledDriver

/-! The concrete pure queue completes by finite work accounting. This proof
uses no fair trace or scheduling hypothesis: every unfinished state processes
the head of its nonempty work list, increasing the amount of completed work. -/

namespace LeanCloud.Proofs.PureReplay
open Lean ReplayModel ReplayInterpreter.Internal

/-- Every valid partial execution can finish using the concrete pure queue. -/
theorem execution_exists {root : Cloud Id Json} {outcome work}
    {evaluation : Evaluation root outcome} (canonical : ProgramWork 0 evaluation work)
    (supported : PureProgram root) {state : State} {spent : Nat}
    (snapshot : RootWorkSnapshot root state spent) :
    ∃ exit finalState, DriverExecution Pure.queue root state exit finalState := by
  generalize remainingEq : work + returnWork outcome - spent = remaining
  induction remaining using Nat.strongRecOn generalizing state spent with
  | ind remaining ih =>
    cases completed : state.completed with
    | some exit =>
      exact ⟨exit, state, .completed completed (by simp [Pure.queue, completed])⟩
    | none =>
      have bounded := snapshot.bounded canonical supported
      simp only [completed, unfinishedWork] at bounded
      obtain ⟨target, member⟩ := snapshot.forget.unfinished_pending completed
      rcases state with ⟨journal, pending, recorded⟩
      dsimp only at completed
      subst recorded
      cases pending with
      | nil => cases member
      | cons head tail =>
        have selected : head ∈ head :: tail := by simp
        obtain ⟨status, structural, ⟨source, cost⟩, queued, recorded⟩ := snapshot
        obtain ⟨updated, status', pending', response, bound, _, _, _, _, stepped⟩ :=
          cost.step_preserves supported (queued.mem_iff.mpr selected)
        have worker : WorkerStep root ⟨journal, head :: tail, none⟩
            (update ⟨updated, head :: tail, none⟩ head response) :=
          .process _ _ _ _ _ _ selected (fun fuel => stepped fuel _)
        have next := (show RootWorkSnapshot root ⟨journal, head :: tail, none⟩ spent from
          ⟨status, structural, ⟨source, cost⟩, queued, recorded⟩).worker_step supported worker
        cases response with
        | done exit =>
          exact ⟨exit, _, .finish selected rfl (fun fuel => stepped fuel _) rfl⟩
        | runnable locations =>
          obtain ⟨exit, finalState, rest⟩ := ih (work + returnWork outcome - (spent + 1))
            (by omega) next rfl
          exact ⟨exit, finalState, .more selected rfl (fun fuel => stepped fuel _) rfl rest⟩

/-- Resuming any valid saved state reaches the direct outcome.
The caller supplies validity of the partial execution, not its eventual result. -/
theorem resume_matches_direct [codec : Codec α]
    (program : ι → Cloud Id α) (input : ι) (law : CodecLaw codec)
    (supported : PureProgram (program input)) {state : State}
    (snapshot : RootSnapshot (codec.encode <$> program input) state) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      (Pure.resume fuel program input state).1 = Pure.direct program input := by
  obtain ⟨outcome, evaluation⟩ := Evaluation.exists _ (supported.map codec.encode)
  obtain ⟨work, canonical⟩ := evaluation.work_exists
  obtain ⟨status, pending, source, queued, completed⟩ := snapshot
  obtain ⟨spent, cost⟩ := source.work_exists
  have measured : RootWorkSnapshot (codec.encode <$> program input) state spent :=
    ⟨status, pending, ⟨source, cost⟩, queued, completed⟩
  obtain ⟨exit, finalState, execution⟩ := execution_exists canonical (supported.map codec.encode) measured
  obtain ⟨bound, correct⟩ := execution.correct (α := α)
  have finished := execution.completed_snapshot (supported.map codec.encode) measured.forget
  refine ⟨bound, ?_⟩
  intro fuel enough
  have actual := congrArg Prod.fst (correct fuel enough)
  exact actual.trans (finished.1.same_output program input law finished.2)

end LeanCloud.Proofs.PureReplay
