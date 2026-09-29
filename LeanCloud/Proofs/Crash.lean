import LeanCloud.CrashModel
import LeanCloud.Protocol

/-! Laws of the crash boundary and restart runner. These do not yet establish
replay-interpreter equivalence across crashes or liveness of a leased queue. -/

namespace LeanCloud.Proofs.CrashRecovery
open CrashModel

theorem atomic_before (operation : δ → α × δ) (durable : δ) (rest calls) :
    (atomic operation).run ⟨durable, ⟨some .before :: rest, calls⟩⟩ =
      (.error .stopped, ⟨durable, ⟨rest, calls + 1⟩⟩) := rfl

theorem atomic_after (operation : δ → α × δ) (durable : δ) (rest calls) :
    (atomic operation).run ⟨durable, ⟨some .after :: rest, calls⟩⟩ =
      (.error .stopped, ⟨(operation durable).2, ⟨rest, calls + 1⟩⟩) := rfl

theorem atomic_success (operation : δ → α × δ) (durable : δ) (rest calls) :
    (atomic operation).run ⟨durable, ⟨none :: rest, calls⟩⟩ =
      (.ok (operation durable).1, ⟨(operation durable).2, ⟨rest, calls + 1⟩⟩) := rfl

/-- The same exception stack as the interpreter: a CloudError handler cannot
convert a worker crash into a recorded error or a successful return value. -/
theorem crash_bypasses_cloudError (fallback : α) (worker : σ) (durable : δ) :
    let action : ExceptT CloudError (StateT σ (CrashM δ)) α := do
      try
        liftM (throw Crash.stopped : CrashM δ α)
      catch _ => pure fallback
    (action.run worker).run durable = (.error .stopped, durable) := rfl

/-- A finite sequence of crashed attempts followed by an ordinary return. Every
attempt starts from the durable state produced by the preceding attempt. -/
inductive Recovers (attempt : CrashM δ α) : δ → α → δ → Prop where
  | returned {start value final} :
      attempt.run start = (.ok value, final) → Recovers attempt start value final
  | crashed {start committed value final} :
      attempt.run start = (.error .stopped, committed) →
      Recovers attempt committed value final → Recovers attempt start value final

theorem restart_eq (retries : Nat) (attempt : CrashM δ α) (durable : δ) :
    (CrashM.restart retries attempt).run durable =
      match attempt.run durable with
      | (.ok value, committed) => (.ok value, committed)
      | (.error crash, committed) =>
        match retries with
        | 0 => (.error crash, committed)
        | retries + 1 => (CrashM.restart retries attempt).run committed :=
  CrashM.restart.eq_1 retries attempt durable

/-- The runner returns an actual attempt's value; it never invents a value or
silently rolls the durable state back after a crash. -/
theorem restart_sound (attempt : CrashM δ α) {retries start value final}
    (returned : (CrashM.restart retries attempt).run start = (.ok value, final)) :
    Recovers attempt start value final := by
  induction retries using Nat.strongRecOn generalizing start with
  | ind retries ih =>
    rw [restart_eq] at returned
    cases observed : attempt.run start with
    | mk result committed =>
      rw [observed] at returned
      cases result with
      | ok result => exact .returned (observed.trans returned)
      | error crash =>
        cases retries with
        | zero => cases returned
        | succ retries => exact .crashed (by cases crash; exact observed) (ih retries (by omega) returned)

/-- Every finite recovery trace needs only finitely many retries. This assumes
the trace exists; queue progress and eventual successful attempts are separate
obligations, not consequences of the exception type. -/
theorem Recovers.eventually_restart {attempt : CrashM δ α} {start value final}
    (trace : Recovers attempt start value final) :
    ∃ bound, ∀ retries, bound ≤ retries →
      (CrashM.restart retries attempt).run start = (.ok value, final) := by
  induction trace with
  | returned observed =>
    exact ⟨0, fun _ _ => by rw [restart_eq, observed]⟩
  | crashed observed _ ih =>
    obtain ⟨bound, enough⟩ := ih
    refine ⟨bound + 1, ?_⟩
    intro retries sufficient
    cases retries with
    | zero => omega
    | succ retries =>
      rw [restart_eq, observed]
      exact enough retries (by omega)

/-- Mapping a returned value retains the same committed state, including on a crash. -/
theorem run_map (f : α → β) (action : M δ α) (state : State δ) :
    (f <$> action).run state = ((action.run state).1.map f, (action.run state).2) := by
  simp only [ExceptT.run, Functor.map, ExceptT.map, ExceptT.mk, StateT.bind, bind, pure]
  cases action state with
  | mk result committed => cases result <;> rfl

/-- A crash stops the continuation while preserving the committed prefix. -/
theorem run_bind (action : M δ α) (next : α → M δ β) (state : State δ) :
    (action >>= next).run state =
      match action.run state with
      | (.error error, committed) => (.error error, committed)
      | (.ok value, committed) => (next value).run committed := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, StateT.bind, bind, pure]
  cases action state with
  | mk result committed => cases result <;> rfl

/-- Changing only the return value does not introduce another atomic boundary. -/
theorem atomic_map (operation : δ → α × δ) (f : α → β) :
    atomic (fun state => let (value, next) := operation state; (f value, next)) =
      f <$> atomic operation := by
  funext state
  change (atomic _).run state = (f <$> atomic operation).run state
  rw [run_map]
  rcases state with ⟨journal, ⟨script, calls⟩⟩
  cases script with
  | nil => rfl
  | cons boundary rest =>
    cases boundary with
    | none => rfl
    | some boundary => cases boundary <;> rfl

/-- An atomic call either commits and returns, or stops on either side of the
commit. A crash consumes a fault entry; no call increases the remaining script. -/
theorem atomic_observation (operation : δ → α × δ) (start : State δ) :
    let (result, final) := (atomic operation).run start
    final.faults.script.length ≤ start.faults.script.length ∧
    match result with
    | .ok value => value = (operation start.durable).1 ∧ final.durable = (operation start.durable).2
    | .error _ => final.faults.script.length < start.faults.script.length ∧
        (final.durable = start.durable ∨ final.durable = (operation start.durable).2) := by
  rcases start with ⟨durable, ⟨script, calls⟩⟩
  cases script with
  | nil => simp [atomic, ExceptT.run]
  | cons boundary rest =>
    cases boundary with
    | none => simp [atomic, ExceptT.run]
    | some boundary => cases boundary <;> simp [atomic, ExceptT.run] <;> trivial

end LeanCloud.Proofs.CrashRecovery
