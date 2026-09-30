import LeanCloud.Proofs.SimulationSafety

/-! Fair progress permits proof-only administrative steps between completed
iterations. Such steps preserve durable state and every unfinished worker.
All commits, replies, crashes, and restarts still use the actual simulator. -/

namespace LeanCloud.Simulation
open LeanEff

universe u v

/-- A schedule may perform an administrative step only on finished workers.
This permits an outer loop to repeat an iteration without changing primitive
execution or the meaning of the simulator's crash/restart events. -/
structure Schedule (start : Fin count → SimM δ α) (advance : Nat → δ → δ) where
  states : Nat → State δ α count
  events : Nat → Option (Event count)
  execution : ∀ n event, events n = some event →
    step start advance event (states n) = .ok (states (n + 1))
  administrative : ∀ n, events n = none →
    (states (n + 1)).durable = (states n).durable ∧
    ∀ worker, ((states n).workers worker).phase ≠ .finished →
      (states (n + 1)).workers worker = (states n).workers worker

/-- Find the first scheduled action, retaining the exact continuation until it
occurs. Other workers are free to change shared state throughout the wait. -/
theorem first_event {σ : Sort u} {ε : Sort v} (states : Nat → σ) (events : Nat → ε) (n : Nat)
    (current : σ) (action : ε) (held : states n = current)
    (fair : (∀ later, n ≤ later → states later = current) →
      ∃ later, n ≤ later ∧ events later = action)
    (preserved : ∀ later, n ≤ later → states later = current →
      events later ≠ action → states (later + 1) = current) :
    ∃ later, n ≤ later ∧ states later = current ∧ events later = action := by
  classical
  have unchanged (offset : Nat) (absent : ∀ i, i < offset → events (n + i) ≠ action) :
      states (n + offset) = current := by
    induction offset with
    | zero => simpa using held
    | succ offset ih =>
      exact preserved (n + offset) (by omega) (ih (fun i inside => absent i (by omega)))
        (absent offset (by omega))
  have occurs : ∃ offset, events (n + offset) = action := by
    apply Classical.byContradiction
    intro never
    have same later (after : n ≤ later) : states later = current := by
      obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le after
      exact unchanged offset (fun i _ equal => never ⟨i, equal⟩)
    obtain ⟨later, after, equal⟩ := fair same
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le after
    exact never ⟨offset, equal⟩
  obtain ⟨offset, equal⟩ := occurs
  induction offset using Nat.strongRecOn with
  | ind offset ih =>
    by_cases earlier : ∃ i, i < offset ∧ events (n + i) = action
    · obtain ⟨i, inside, occurred⟩ := earlier
      exact ih i inside occurred
    · exact ⟨n + offset, by omega,
        unchanged _ (fun i inside occurred => earlier ⟨i, inside, occurred⟩), equal⟩

namespace Schedule
variable {start : Fin count → SimM δ α} {advance : Nat → δ → δ}

structure WeaklyFair (trace : Schedule start advance) : Prop where
  commit : ∀ worker n,
    (∀ later, n ≤ later → ((trace.states later).workers worker).phase = .waiting) →
    ∃ later, n ≤ later ∧ trace.events later = some (.commit worker)
  resume : ∀ worker n,
    (∀ later, n ≤ later → ((trace.states later).workers worker).phase = .responding) →
    ∃ later, n ≤ later ∧ trace.events later = some (.resume worker)
  restart : ∀ worker n,
    (∀ later, n ≤ later → ((trace.states later).workers worker).phase = .stopped) →
    ∃ later, n ≤ later ∧ trace.events later = some (.restart worker)

def NoCrashesAfter (trace : Schedule start advance) (worker : Fin count) (cut : Nat) : Prop :=
  ∀ n, cut ≤ n → trace.events n ≠ some (.crash worker)

private theorem step_waiting_unchanged {state final : State δ α count} {worker : Fin count}
    {operation : δ → β × δ} {next : ArrsF (Atomic δ) β α} {event : Event count}
    (held : state.workers worker = .waiting operation next)
    (executed : step start advance event state = .ok final)
    (noCommit : event ≠ .commit worker) (noCrash : event ≠ .crash worker) :
    final.workers worker = .waiting operation next := by
  cases event with
  | advanceTime elapsed => cases executed; exact held
  | commit other =>
    have different : worker ≠ other := by intro same; subst other; exact noCommit rfl
    cases seen : state.workers other <;> simp only [step, seen] at executed
    all_goals cases executed
    simpa only [State.setWorker_other _ _ _ _ different] using held
  | resume other | restart other =>
    by_cases same : worker = other
    · subst other; simp [step, held] at executed
    · cases seen : state.workers other <;> simp only [step, seen] at executed
      all_goals cases executed
      simpa only [State.setWorker_other _ _ _ _ same] using held
  | crash other =>
    have different : worker ≠ other := by intro same; subst other; exact noCrash rfl
    cases seen : state.workers other <;> simp only [step, seen] at executed
    all_goals cases executed
    all_goals simpa only [State.setWorker_other _ _ _ _ different] using held

private theorem step_responding_unchanged {state final : State δ α count} {worker : Fin count}
    {value : β} {next : ArrsF (Atomic δ) β α} {event : Event count}
    (held : state.workers worker = .responding value next)
    (executed : step start advance event state = .ok final)
    (noResume : event ≠ .resume worker) (noCrash : event ≠ .crash worker) :
    final.workers worker = .responding value next := by
  cases event with
  | advanceTime elapsed => cases executed; exact held
  | resume other =>
    have different : worker ≠ other := by intro same; subst other; exact noResume rfl
    cases seen : state.workers other <;> simp only [step, seen] at executed
    all_goals cases executed
    simpa only [State.setWorker_other _ _ _ _ different] using held
  | commit other | restart other =>
    by_cases same : worker = other
    · subst other; simp [step, held] at executed
    · cases seen : state.workers other <;> simp only [step, seen] at executed
      all_goals cases executed
      simpa only [State.setWorker_other _ _ _ _ same] using held
  | crash other =>
    have different : worker ≠ other := by intro same; subst other; exact noCrash rfl
    cases seen : state.workers other <;> simp only [step, seen] at executed
    all_goals cases executed
    all_goals simpa only [State.setWorker_other _ _ _ _ different] using held

private theorem step_stopped_unchanged {state final : State δ α count} {worker : Fin count}
    {event : Event count} (held : state.workers worker = .stopped)
    (executed : step start advance event state = .ok final) (noRestart : event ≠ .restart worker) :
    final.workers worker = .stopped := by
  cases event with
  | advanceTime elapsed => cases executed; exact held
  | restart other =>
    have different : worker ≠ other := by intro same; subst other; exact noRestart rfl
    cases seen : state.workers other <;> simp only [step, seen] at executed
    all_goals cases executed
    simpa only [State.setWorker_other _ _ _ _ different] using held
  | commit other | resume other | crash other =>
    by_cases same : worker = other
    · subst other; simp [step, held] at executed
    · cases seen : state.workers other <;> simp only [step, seen] at executed
      all_goals cases executed
      all_goals simpa only [State.setWorker_other _ _ _ _ same] using held

private theorem waiting_unchanged (trace : Schedule start advance) {n worker}
    {operation : δ → β × δ} {next : ArrsF (Atomic δ) β α}
    (held : (trace.states n).workers worker = .waiting operation next)
    (absent : trace.events n ≠ some (.commit worker)) (noCrash : trace.events n ≠ some (.crash worker)) :
    (trace.states (n + 1)).workers worker = .waiting operation next := by
  cases event : trace.events n with
  | none => exact ((trace.administrative n event).2 worker (by simp [held, Worker.phase])).trans held
  | some action =>
    exact step_waiting_unchanged held (trace.execution n action event)
      (fun same => absent (event.trans (congrArg some same)))
      (fun same => noCrash (event.trans (congrArg some same)))

private theorem responding_unchanged (trace : Schedule start advance) {n worker}
    {value : β} {next : ArrsF (Atomic δ) β α}
    (held : (trace.states n).workers worker = .responding value next)
    (absent : trace.events n ≠ some (.resume worker)) (noCrash : trace.events n ≠ some (.crash worker)) :
    (trace.states (n + 1)).workers worker = .responding value next := by
  cases event : trace.events n with
  | none => exact ((trace.administrative n event).2 worker (by simp [held, Worker.phase])).trans held
  | some action =>
    exact step_responding_unchanged held (trace.execution n action event)
      (fun same => absent (event.trans (congrArg some same)))
      (fun same => noCrash (event.trans (congrArg some same)))

private theorem stopped_unchanged (trace : Schedule start advance) {n worker}
    (held : (trace.states n).workers worker = .stopped) (absent : trace.events n ≠ some (.restart worker)) :
    (trace.states (n + 1)).workers worker = .stopped := by
  cases event : trace.events n with
  | none => exact ((trace.administrative n event).2 worker (by simp [held, Worker.phase])).trans held
  | some action =>
    exact step_stopped_unchanged held (trace.execution n action event)
      (fun same => absent (event.trans (congrArg some same)))

/-- Fair scheduling executes any certified finite prefix of this worker after
its crashes stop. The target can be an internal milestone; the worker need not
finish its whole attempt. Other workers may continue changing shared state. -/
theorem eventually_reaches (trace : Schedule start advance) (fair : trace.WeaklyFair)
    (worker : Fin count) {valid : δ → Prop} {grows : δ → δ → Prop} {goal : Worker δ α → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (kept : ∀ n, valid (trace.states n).durable)
    (growth : ∀ before after, before ≤ after → grows (trace.states before).durable (trace.states after).durable)
    {current : Worker δ α} {state : δ} (progress : Reaches valid grows goal current state)
    (n : Nat) (held : (trace.states n).workers worker = current)
    (noCrash : trace.NoCrashesAfter worker n)
    (prior : grows state (trace.states n).durable) :
    ∃ later, n ≤ later ∧ goal ((trace.states later).workers worker) (trace.states later).durable := by
  induction progress generalizing n with
  | @waiting β operation next state remaining ih =>
    obtain ⟨later, after, held, scheduled⟩ := first_event (fun index => (trace.states index).workers worker) trace.events n _ (some (.commit worker)) held
      (fun same => fair.commit worker n (fun later after => by rw [same later after]; rfl))
      (fun later after held absent => trace.waiting_unchanged held absent (noCrash later after))
    have executed := trace.execution later _ scheduled
    simp only [step, held] at executed
    have remaining : (trace.states (later + 1)).workers worker = .responding (operation (trace.states later).durable).1 next := by
      rw [← Except.ok.inj executed]
      exact State.setWorker_same _ _ _
    have durable : (trace.states (later + 1)).durable = (operation (trace.states later).durable).2 := by
      rw [← Except.ok.inj executed]
    obtain ⟨done, afterDone, reached⟩ := ih (trace.states later).durable (kept later)
      (trans prior (growth n later after)) (later + 1) remaining
      (fun index beyond => noCrash index (by omega))
      (by rw [durable]; exact refl _)
    exact ⟨done, by omega, reached⟩
  | @responding β value next state remaining ih =>
    obtain ⟨later, after, held, scheduled⟩ := first_event (fun index => (trace.states index).workers worker) trace.events n _ (some (.resume worker)) held
      (fun same => fair.resume worker n (fun later after => by rw [same later after]; rfl))
      (fun later after held absent => trace.responding_unchanged held absent (noCrash later after))
    have executed := trace.execution later _ scheduled
    simp only [step, held] at executed
    have remaining : (trace.states (later + 1)).workers worker = .ofProgram (ArrsF.apply next value) := by
      rw [← Except.ok.inj executed]
      exact State.setWorker_same _ _ _
    have durable : (trace.states (later + 1)).durable = (trace.states later).durable := by
      rw [← Except.ok.inj executed]
      rfl
    obtain ⟨done, afterDone, reached⟩ := ih (trace.states later).durable (kept later)
      (trans prior (growth n later after)) (later + 1) remaining
      (fun index beyond => noCrash index (by omega)) (by rw [durable]; exact refl _)
    exact ⟨done, by omega, reached⟩
  | arrived reached => exact ⟨n, Nat.le_refl _, held ▸ reached _ (kept n) prior⟩

private theorem finishes_running (trace : Schedule start advance) (fair : trace.WeaklyFair)
    (worker : Fin count) {valid : δ → Prop} {grows : δ → δ → Prop} {post : α → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (kept : ∀ n, valid (trace.states n).durable)
    (growth : ∀ before after, before ≤ after → grows (trace.states before).durable (trace.states after).durable)
    {current : Worker δ α} {state : δ} (safe : Safe valid grows post current state)
    (n : Nat) (held : (trace.states n).workers worker = current)
    (noCrash : trace.NoCrashesAfter worker n) (running : current ≠ .stopped)
    (prior : grows state (trace.states n).durable) :
    ∃ later value, n ≤ later ∧ (trace.states later).workers worker = .finished value ∧
      post value (trace.states later).durable := by
  obtain ⟨later, after, value, finished, result⟩ := trace.eventually_reaches fair worker refl trans kept growth
    (safe.reaches_return running) n held noCrash prior
  exact ⟨later, value, after, finished, result⟩

/-- A stopped worker is restarted with a fresh attempt; a paused worker retains
its continuation. Either eventually returns after its last crash. This proves
termination of the attempt, which can still return a fuel-exhaustion error. -/
theorem finishes (trace : Schedule start advance) (fair : trace.WeaklyFair)
    (worker : Fin count) {valid : δ → Prop} {grows : δ → δ → Prop} {post : α → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (kept : ∀ n, valid (trace.states n).durable)
    (growth : ∀ before after, before ≤ after → grows (trace.states before).durable (trace.states after).durable)
    (fresh : ∀ state, valid state → Safe valid grows post (.ofProgram (start worker)) state)
    (n : Nat) (safe : Safe valid grows post ((trace.states n).workers worker) (trace.states n).durable)
    (noCrash : trace.NoCrashesAfter worker n) :
    ∃ later value, n ≤ later ∧ (trace.states later).workers worker = .finished value ∧
      post value (trace.states later).durable := by
  by_cases stopped : (trace.states n).workers worker = .stopped
  · obtain ⟨later, after, held, scheduled⟩ := first_event (fun index => (trace.states index).workers worker) trace.events n .stopped (some (.restart worker)) stopped
      (fun same => fair.restart worker n (fun later after => by rw [same later after]; rfl))
      (fun later _ held absent => trace.stopped_unchanged held absent)
    have executed := trace.execution later _ scheduled
    simp only [step, held] at executed
    have remaining : (trace.states (later + 1)).workers worker = .ofProgram (start worker) := by
      rw [← Except.ok.inj executed]
      exact State.setWorker_same _ _ _
    have active : Worker.ofProgram (start worker) ≠ .stopped := by
      cases start worker with
      | pure value => intro impossible; cases impossible
      | impure operation rest => cases operation; intro impossible; cases impossible
    obtain ⟨done, value, afterDone, returned, result⟩ := trace.finishes_running fair worker refl trans kept growth
      (fresh _ (kept (later + 1))) (later + 1) remaining
      (fun index beyond => noCrash index (by omega)) active (refl _)
    exact ⟨done, value, by omega, returned, result⟩
  · exact trace.finishes_running fair worker refl trans kept growth safe n rfl noCrash stopped (refl _)

end Schedule
end LeanCloud.Simulation
