import LeanCloud.Proofs.BackendLocated

namespace LeanCloud.Backend.Proofs
open LeanEff Execution

/-- Every existing worker finishes its current computation or a replacement
attempt after its last crash. Neither workflow success nor delivery is assumed. -/
theorem worker_returns {programs : Array (M α)}
    (trace : Execution.Schedule programs) (fair : trace.WeaklyFair)
    {valid : Backend.State → Prop} {grows : Backend.State → Backend.State → Prop}
    {post : Nat → α → Backend.State → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (kept : ∀ time, AllSafe valid grows post (trace.states time))
    (growth : ∀ first last, first ≤ last → grows (trace.states first).services (trace.states last).services)
    (fresh : ∀ index program, programs[index]? = some program → ∀ state,
      valid state → ProgramSafe valid grows (post index) program state)
    (located : ∀ time, Located (trace.states time))
    (worker time : Nat) (program : M α) (found : programs[worker]? = some program)
    (current : Execution.Worker α) (held : (trace.states time).workers[worker]? = some current)
    (noCrash : trace.NoCrashesAfter worker time) :
    ∃ later attempt value, time ≤ later ∧
      (trace.states later).workers[worker]? = some ⟨attempt, .finished value⟩ ∧
      post worker value (trace.states later).services := by
  obtain ⟨attempt, status⟩ := current
  cases status with
  | finished value =>
    have safe := (kept time).workers worker _ held
    cases safe with
    | pure done => exact ⟨time, attempt, value, Nat.le_refl _, held, done _ (kept time).services (refl _)⟩
  | stopped =>
    obtain ⟨restartedAt, beyond, stopped, event⟩ := trace.eventually_restart fair held
    have performed := trace.execution restartedAt _ event
    have activated : trace.states (restartedAt + 1) =
        activate ⟨worker, attempt + 1⟩ program (trace.states restartedAt) := by
      cases performed with
      | restart performed => simpa [Execution.step, stopped, found, pure, Except.pure] using performed.symm
    have continuing : Continues ⟨worker, attempt + 1⟩ (Program.ofEff program) (trace.states (restartedAt + 1)) := by
      rw [activated]
      exact activate_continues _ _ _ (Array.getElem?_eq_some_iff.mp stopped).choose
    obtain ⟨later, value, beyondReturn, finished, result⟩ := Safe.eventually_returns
      (grows := grows) trace fair (fun a b => trans a b) (fun n => (kept n).services) growth
      (fresh worker program found _ (kept (restartedAt + 1)).services) (restartedAt + 1) continuing
      (fun n after => noCrash n (by omega)) (refl _)
    exact ⟨later, attempt + 1, value, by omega, finished, result⟩
  | waiting id =>
    obtain ⟨call, stored, caller⟩ := located time worker attempt id held
    have certified := (kept time).calls id call stored
    cases call with
    | retired => cases caller
    | pending owner operation next =>
      cases next with
      | none => cases caller
      | some next =>
        have equal := Option.some.inj caller
        subst owner
        have safe : Safe valid grows (post worker) (.request operation (Program.ofArrs next)) (trace.states time).services :=
          .request certified.1 (fun before value after valid growth law => certified.2 before value after valid growth law next rfl)
        obtain ⟨later, value, beyond, finished, result⟩ := Safe.eventually_returns
          (grows := grows) trace fair (fun a b => trans a b) (fun n => (kept n).services) growth safe time
          (Continues.request ⟨held, stored⟩) noCrash (refl _)
        exact ⟨later, attempt, value, beyond, finished, result⟩
    | committed owner operation value next =>
      cases next with
      | none => cases caller
      | some next =>
        have equal := Option.some.inj caller
        subst owner
        obtain ⟨later, value, beyond, finished, result⟩ := Safe.responding_returns
          (grows := grows) trace fair (fun a b => trans a b) (fun n => (kept n).services) growth
          (certified next rfl) time ⟨held, stored⟩ noCrash (refl _)
        exact ⟨later, attempt, value, beyond, finished, result⟩

end LeanCloud.Backend.Proofs
