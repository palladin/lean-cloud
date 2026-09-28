import LeanCloud.Proofs.SnapshotStep
import LeanCloud.Proofs.ReplayExecution

/-! Observations of the actual worker, allowing any pending item to be selected. -/
namespace LeanCloud.Proofs
open Lean ReplayModel ReplayInterpreter.Internal

def outcomeExit : Except CloudError Json → Exit
  | .ok value => .success value
  | .error error => .failure error

def RootSnapshot (root : Cloud Id Json) (state : State) : Prop :=
  ∃ status pending,
    ReplaySnapshot state.journal root #[] 0 0 status pending ∧
    pending.Perm state.pending ∧ state.completed = status.map outcomeExit

theorem RootSnapshot.initial (root : Cloud Id Json) :
    RootSnapshot root ⟨Journal.empty, [Location.root], none⟩ :=
  ⟨none, [Location.root], .initial root, .refl _, rfl⟩

/-- A selected worker call with sufficient fuel; its response determines the
new pending work and completion record. -/
inductive WorkerStep (root : Cloud Id Json) : State → State → Prop where
  | process (journal updated : Journal) (pending : List Location) (target : Location)
      (response : StepResult) (bound : Nat) (selected : target ∈ pending)
      (executed : ∀ fuel,
        (step db noBlobs (fuel + bound) root target).run ⟨journal, pending, none⟩ =
          (.ok response, ⟨updated, pending, none⟩)) :
      WorkerStep root ⟨journal, pending, none⟩ (update ⟨updated, pending, none⟩ target response)

def RootWorkSnapshot (root : Cloud Id Json)
    (state : State) (spent : Nat) : Prop :=
  ∃ status pending,
    (∃ snapshot : ReplaySnapshot state.journal root #[] 0 0 status pending, SnapshotWork snapshot spent) ∧
    pending.Perm state.pending ∧
    state.completed = status.map outcomeExit

theorem RootWorkSnapshot.initial (root : Cloud Id Json) :
    RootWorkSnapshot root ⟨Journal.empty, [Location.root], none⟩ 0 :=
  ⟨none, [Location.root], ⟨_, .pending root #[] 0 0 (.empty _ _)⟩, .refl _, rfl⟩

theorem RootWorkSnapshot.forget {root : Cloud Id Json}
    {state spent} (snapshot : RootWorkSnapshot root state spent) :
    RootSnapshot root state := by
  obtain ⟨status, pending, ⟨source, _⟩, rest⟩ := snapshot
  exact ⟨status, pending, source, rest⟩

theorem RootWorkSnapshot.worker_step {root : Cloud Id Json}
    {state spent nextState}
    (snapshot : RootWorkSnapshot root state spent) (supported : PureProgram root)
    (worker : WorkerStep root state nextState) :
    RootWorkSnapshot root nextState (spent + 1) := by
  cases worker with
  | process journal updated pending target response bound selected executed =>
    obtain ⟨status, structural, ⟨source, sourceCost⟩, queued, completed⟩ := snapshot
    have member : target ∈ structural := queued.mem_iff.mpr selected
    obtain ⟨saved, outcome, after, reply, cost,
      ⟨replacement, replacementCost⟩, _, _, emission, actual⟩ := sourceCost.step_preserves supported member
    have same := (executed cost).symm.trans (by simpa only [Nat.add_comm] using actual bound pending)
    have replyEq := Except.ok.inj (congrArg Prod.fst same)
    have journalEq := congrArg (fun r => r.2.journal) same
    dsimp only at journalEq
    subst reply saved
    refine ⟨outcome, after, (by cases response <;> exact ⟨replacement, replacementCost⟩),
      ?_, ?_⟩
    · cases outcome with
      | none =>
        obtain ⟨published, rfl, changed⟩ := emission
        exact changed.trans ((queued.erase target).append_left published.toList)
      | some value =>
        obtain ⟨reply, _, rfl⟩ := emission
        cases value <;> subst response <;> exact .refl _
    · cases outcome with
      | none => obtain ⟨published, rfl, _⟩ := emission; rfl
      | some value =>
        obtain ⟨reply, _, _⟩ := emission
        cases value <;> subst response <;> rfl

theorem RootSnapshot.worker_step {root : Cloud Id Json} {state nextState}
    (snapshot : RootSnapshot root state) (supported : PureProgram root)
    (worker : WorkerStep root state nextState) : RootSnapshot root nextState := by
  obtain ⟨status, pending, source, queued, completed⟩ := snapshot
  obtain ⟨spent, cost⟩ := source.work_exists
  have measured : RootWorkSnapshot root state spent := ⟨status, pending, ⟨source, cost⟩, queued, completed⟩
  exact (measured.worker_step supported worker).forget

theorem RootSnapshot.completed_evaluation {root : Cloud Id Json} {state exit}
    (snapshot : RootSnapshot root state) (completed : state.completed = some exit) :
    ∃ outcome, exit = outcomeExit outcome ∧ Evaluation root outcome := by
  obtain ⟨status, pending, source, _, stored⟩ := snapshot
  rw [completed] at stored
  cases status with
  | none => cases stored
  | some value => exact ⟨value, Option.some.inj stored, source.evaluation rfl⟩

/-- A completed root snapshot determines the direct interpreter's result. -/
theorem RootSnapshot.same_output [codec : Codec α]
    (program : ι → Cloud Id α) (input : ι) {state : State} {exit : Exit}
    (law : CodecLaw codec)
    (snapshot : RootSnapshot (codec.encode <$> program input) state)
    (completed : state.completed = some exit) :
    decodeExit (α := α) exit = direct (program input) := by
  obtain ⟨encoded, exitEq, evaluation⟩ := snapshot.completed_evaluation completed
  obtain ⟨outcome, original, encodedEq⟩ := evaluation.map_cases (program input) codec.encode
  rw [original.result, exitEq, encodedEq]
  cases outcome with
  | error error => rfl
  | ok value => exact decodeExit_encoded law value

end LeanCloud.Proofs
