import LeanCloud.Simulation

/-! Saved replies and isolation of worker-local scheduling events. -/

namespace LeanCloud.Simulation
open LeanEff

@[simp] theorem State.setWorker_same (state : State δ α count) (worker : Fin count)
    (next : Worker δ α) : (state.setWorker worker next).workers worker = next := by
  simp [State.setWorker]

@[simp] theorem State.setWorker_other (state : State δ α count) (worker other : Fin count)
    (next : Worker δ α) (different : other ≠ worker) :
    (state.setWorker worker next).workers other = state.workers other := by
  simp [State.setWorker, different]

/-- Suspend/resume uses the original reply, and changes no shared storage. -/
theorem resume_reply (start : Fin count → SimM δ α) (advance : Nat → δ → δ)
    (state : State δ α count) (worker : Fin count) (value : β)
    (next : ArrsF (Atomic δ) β α)
    (waiting : state.workers worker = .responding value next) :
    step start advance (.resume worker) state =
      .ok (state.setWorker worker (.ofProgram (ArrsF.apply next value))) := by
  simp [step, waiting]

/-- A crash/restart replaces only the selected worker. In particular, it does
not release its lease, change shared records, or resume its old continuation. -/
theorem crash_restart (start : Fin count → SimM δ α) (advance : Nat → δ → δ)
    (state : State δ α count) (worker : Fin count)
    (active : (state.workers worker).phase = .waiting ∨
      (state.workers worker).phase = .responding) :
    run start advance [.crash worker, .restart worker] state =
      .ok (state.setWorker worker (.ofProgram (start worker))) := by
  cases observed : state.workers worker <;>
    simp [Worker.phase, observed] at active ⊢
  all_goals
    simp +contextual [run, List.foldlM, step, observed, State.setWorker, bind, Except.bind, pure, Except.pure]

end LeanCloud.Simulation
