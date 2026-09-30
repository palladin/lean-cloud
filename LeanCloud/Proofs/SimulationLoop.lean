import LeanCloud.Proofs.SimulationSchedule

/-! Proof-only repetition of finite worker iterations. `repeatIteration` represents the
outer loop's next iteration, not a crash recovery event. It is allowed only at
an accepted iteration result and makes no durable change. All other events use
the original simulator. ConcurrentRealization proves finite-fuel correspondence
for replay iterations. -/

namespace LeanCloud.Simulation.Repeated

inductive Event (count : Nat) where
  | ordinary : Simulation.Event count → Event count
  | repeatIteration : Fin count → Event count

inductive Error where
  | ordinary : Simulation.Error → Error
  | notRepeatable

def step (start : Fin count → SimM δ α) (clock : Nat → δ → δ) (again : α → Bool)
    (event : Event count) (state : Simulation.State δ α count) : Except Error (Simulation.State δ α count) :=
  match event with
  | .ordinary event => (Simulation.step start clock event state).mapError .ordinary
  | .repeatIteration worker =>
    match state.workers worker with
    | .finished value =>
      if again value then .ok (state.setWorker worker (.ofProgram (start worker))) else .error .notRepeatable
    | _ => .error .notRepeatable

def run (start : Fin count → SimM δ α) (clock : Nat → δ → δ) (again : α → Bool)
    (events : List (Event count)) (state : Simulation.State δ α count) : Except Error (Simulation.State δ α count) :=
  events.foldlM (fun state event => step start clock again event state) state

private theorem ordinary_eq_ok {action : Except Simulation.Error α} {value : α}
    (executed : action.mapError Error.ordinary = .ok value) : action = .ok value := by
  cases action with
  | error error => cases executed
  | ok result => exact congrArg Except.ok (Except.ok.inj executed)

private theorem finished_unchanged {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}
    {state final : Simulation.State δ α count} {worker : Fin count} {value : α} {event : Event count}
    (held : state.workers worker = .finished value)
    (executed : step start clock again event state = .ok final)
    (absent : event ≠ .repeatIteration worker) : final.workers worker = .finished value := by
  cases event with
  | ordinary event =>
    have executed := ordinary_eq_ok executed
    cases event with
    | advanceTime elapsed => cases executed; exact held
    | commit other | resume other | crash other | restart other =>
      by_cases same : worker = other
      · subst other; simp [Simulation.step, held] at executed
      · cases seen : state.workers other <;> simp only [Simulation.step, seen] at executed
        all_goals cases executed
        all_goals simpa only [State.setWorker_other _ _ _ _ same] using held
  | repeatIteration other =>
    have different : worker ≠ other := by intro same; subst other; exact absent rfl
    cases seen : state.workers other <;> simp only [step, seen] at executed
    case finished result =>
      split at executed
      next allowed =>
        cases executed
        simpa only [State.setWorker_other _ _ _ _ different] using held
      next refused => cases executed
    all_goals cases executed

structure Trace (start : Fin count → SimM δ α) (clock : Nat → δ → δ) (again : α → Bool) where
  states : Nat → Simulation.State δ α count
  events : Nat → Event count
  execution : ∀ n, step start clock again (events n) (states n) = .ok (states (n + 1))

namespace Trace
variable {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}

def schedule (trace : Trace start clock again) : Schedule start clock where
  states := trace.states
  events n := match trace.events n with
    | .ordinary event => some event
    | .repeatIteration _ => none
  execution n event same := by
    have executed := trace.execution n
    cases observed : trace.events n with
    | ordinary action =>
      simp only [observed, Option.some.injEq] at same
      subst action
      exact ordinary_eq_ok (by simpa only [step, observed] using executed)
    | repeatIteration worker => simp [observed] at same
  administrative n silent := by
    have executed := trace.execution n
    cases event : trace.events n with
    | ordinary action => simp [event] at silent
    | repeatIteration index =>
      cases held : (trace.states n).workers index <;> simp only [step, event, held] at executed
      case finished value =>
        split at executed
        next allowed =>
          rw [← Except.ok.inj executed]
          refine ⟨rfl, ?_⟩
          intro worker unfinished
          by_cases same : worker = index
          · subst worker; simp [held, Worker.phase] at unfinished
          · exact State.setWorker_other _ _ _ _ same
        next refused => cases executed
      all_goals cases executed

/-- Worker fairness and iteration repetition are separate from queue delivery.
No fairness field assumes that an iteration selects work or completes a run. -/
structure WeaklyFair (trace : Trace start clock again) : Prop where
  workers : trace.schedule.WeaklyFair
  iterations : ∀ worker n,
    (∀ later, n ≤ later → ∃ value, (trace.states later).workers worker = .finished value ∧ again value = true) →
    ∃ later, n ≤ later ∧ trace.events later = .repeatIteration worker

def NoCrashesAfter (trace : Trace start clock again) (worker : Fin count) (cut : Nat) : Prop :=
  trace.schedule.NoCrashesAfter worker cut

/-- A successful unfinished iteration cannot stay parked forever when
repetition is fair. The next iteration starts without a durable mutation or
an invented crash. Errors and terminal results need not satisfy `again`. -/
theorem eventually_repeats (trace : Trace start clock again) (fair : trace.WeaklyFair)
    (worker : Fin count) (cut : Nat) (value : α)
    (held : (trace.states cut).workers worker = .finished value) (repeatable : again value = true) :
    ∃ later, cut < later ∧ (trace.states later).workers worker = .ofProgram (start worker) := by
  obtain ⟨atTime, after, waiting, scheduled⟩ := first_event
    (fun n => (trace.states n).workers worker) trace.events cut (.finished value) (.repeatIteration worker) held
    (fun same => fair.iterations worker cut (fun n beyond => ⟨value, same n beyond, repeatable⟩))
    (fun n _ present absent => finished_unchanged present (trace.execution n) absent)
  have executed := trace.execution atTime
  simp only [step, scheduled, waiting, repeatable, ↓reduceIte] at executed
  refine ⟨atTime + 1, by omega, ?_⟩
  rw [← Except.ok.inj executed]
  exact State.setWorker_same _ _ _

theorem run_prefix (trace : Trace start clock again) (n : Nat) :
    run start clock again (List.ofFn fun i : Fin n => trace.events i.val) (trace.states 0) = .ok (trace.states n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ_last, run, List.foldlM_append]
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
    change (run start clock again (List.ofFn fun i : Fin n => trace.events i.val) (trace.states 0) >>=
      fun state => step start clock again (trace.events n) state) = _
    rw [ih]
    exact trace.execution n

end Trace

/-- Repetition reuses the same finite iteration at the current durable state.
It cannot alter another worker's reply, continuation, or crash state. -/
theorem step_safe {valid : δ → Prop} {grows : δ → δ → Prop}
    (refl : ∀ state, grows state state) (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (start : Fin count → SimM δ α) (clock : Nat → δ → δ) (again : α → Bool)
    (post : Fin count → α → δ → Prop)
    (fresh : ∀ worker state, valid state → Safe valid grows (post worker) (.ofProgram (start worker)) state)
    (time : ∀ elapsed state, valid state → valid (clock elapsed state) ∧ grows state (clock elapsed state))
    (event : Event count) {state final : Simulation.State δ α count}
    (safe : AllSafe valid grows post state) (executed : step start clock again event state = .ok final) :
    grows state.durable final.durable ∧ AllSafe valid grows post final := by
  cases event with
  | ordinary event => exact Simulation.step_safe refl trans start clock post fresh time event safe (ordinary_eq_ok executed)
  | repeatIteration worker =>
    cases held : state.workers worker <;> simp only [step, held] at executed
    case finished value =>
      split at executed
      next allowed =>
        cases executed
        exact ⟨refl _, safe.update trans worker _ _ safe.1 (refl _) (fresh worker _ safe.1)⟩
      next refused => cases executed
    all_goals cases executed

theorem Trace.invariants {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}
    (trace : Trace start clock again) {valid : δ → Prop} {grows : δ → δ → Prop} {post : Fin count → α → δ → Prop}
    (refl : ∀ state, grows state state) (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (fresh : ∀ worker state, valid state → Safe valid grows (post worker) (.ofProgram (start worker)) state)
    (time : ∀ elapsed state, valid state → valid (clock elapsed state) ∧ grows state (clock elapsed state))
    (initial : AllSafe valid grows post (trace.states 0)) :
    (∀ n, AllSafe valid grows post (trace.states n)) ∧
      ∀ before after, before ≤ after → grows (trace.states before).durable (trace.states after).durable := by
  have kept n : AllSafe valid grows post (trace.states n) := by
    induction n with
    | zero => exact initial
    | succ n ih => exact (step_safe refl trans start clock again post fresh time (trace.events n) ih (trace.execution n)).2
  refine ⟨kept, ?_⟩
  intro before after later
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
  induction offset with
  | zero => exact refl _
  | succ offset ih =>
    exact trans (ih (by omega)) (step_safe refl trans start clock again post fresh time
      (trace.events (before + offset)) (kept _) (trace.execution _)).1

end LeanCloud.Simulation.Repeated
