import LeanCloud.Proofs.SimulationSchedule

/-! Progress of the actual suspended workers. Fairness schedules continuously
enabled commit, reply delivery, and restart events. It does not assume that an
attempt succeeds, that a queue item is selected, or that a workflow completes. -/

namespace LeanCloud.Simulation
open LeanEff

/-- An infinite legal execution; every finite prefix is an ordinary simulator
run. The environment may interleave workers and advance time arbitrarily. -/
structure Trace (start : Fin count → SimM δ α) (advance : Nat → δ → δ) where
  states : Nat → State δ α count
  events : Nat → Event count
  execution : ∀ n, step start advance (events n) (states n) = .ok (states (n + 1))

namespace Trace
variable {start : Fin count → SimM δ α} {advance : Nat → δ → δ}

/-- Ordinary weak fairness for the three worker actions. A continuously enabled
action cannot be postponed forever. Crashing is never required by fairness. -/
structure WeaklyFair (trace : Trace start advance) : Prop where
  commit : ∀ worker n,
    (∀ later, n ≤ later → ((trace.states later).workers worker).phase = .waiting) →
    ∃ later, n ≤ later ∧ trace.events later = .commit worker
  resume : ∀ worker n,
    (∀ later, n ≤ later → ((trace.states later).workers worker).phase = .responding) →
    ∃ later, n ≤ later ∧ trace.events later = .resume worker
  restart : ∀ worker n,
    (∀ later, n ≤ later → ((trace.states later).workers worker).phase = .stopped) →
    ∃ later, n ≤ later ∧ trace.events later = .restart worker

/-- Only this worker's crashes must stop; other workers may still crash. -/
def NoCrashesAfter (trace : Trace start advance) (worker : Fin count) (cut : Nat) : Prop :=
  ∀ n, cut ≤ n → trace.events n ≠ .crash worker

theorem run_prefix (trace : Trace start advance) (n : Nat) :
    run start advance (List.ofFn fun i : Fin n => trace.events i.val)
      (trace.states 0) = .ok (trace.states n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ_last, run, List.foldlM_append]
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
    change (run start advance (List.ofFn fun i : Fin n => trace.events i.val)
      (trace.states 0) >>= fun state => step start advance (trace.events n) state) = _
    rw [ih]
    exact trace.execution n

/-- An original simulator trace has no administrative steps. -/
def schedule (trace : Trace start advance) : Schedule start advance where
  states := trace.states
  events n := some (trace.events n)
  execution n event same := by cases same; exact trace.execution n
  administrative _ impossible := by cases impossible

theorem schedule_fair (trace : Trace start advance) (fair : trace.WeaklyFair) : trace.schedule.WeaklyFair := by
  constructor
  · intro worker n enabled
    obtain ⟨later, after, scheduled⟩ := fair.commit worker n enabled
    exact ⟨later, after, congrArg some scheduled⟩
  · intro worker n enabled
    obtain ⟨later, after, scheduled⟩ := fair.resume worker n enabled
    exact ⟨later, after, congrArg some scheduled⟩
  · intro worker n enabled
    obtain ⟨later, after, scheduled⟩ := fair.restart worker n enabled
    exact ⟨later, after, congrArg some scheduled⟩

theorem schedule_noCrashes (trace : Trace start advance) (worker : Fin count) (cut : Nat)
    (noCrash : trace.NoCrashesAfter worker cut) : trace.schedule.NoCrashesAfter worker cut :=
  fun n after same => noCrash n after (Option.some.inj same)

/-- Fair scheduling executes any certified finite prefix of this worker after
its crashes stop. The target can be an internal milestone; the worker need not
finish its whole attempt. Other workers may continue changing shared state. -/
theorem eventually_reaches (trace : Trace start advance) (fair : trace.WeaklyFair)
    (worker : Fin count) {valid : δ → Prop} {grows : δ → δ → Prop} {goal : Worker δ α → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (kept : ∀ n, valid (trace.states n).durable)
    (growth : ∀ before after, before ≤ after → grows (trace.states before).durable (trace.states after).durable)
    {current : Worker δ α} {state : δ} (progress : Reaches valid grows goal current state)
    (n : Nat) (held : (trace.states n).workers worker = current)
    (noCrash : trace.NoCrashesAfter worker n)
    (prior : grows state (trace.states n).durable) :
    ∃ later, n ≤ later ∧ goal ((trace.states later).workers worker) (trace.states later).durable :=
  trace.schedule.eventually_reaches (trace.schedule_fair fair) worker refl trans kept growth progress n held
    (trace.schedule_noCrashes worker n noCrash) prior

/-- Lift the existing finite safety rule to all times and all intervals of a
legal trace. Interference remains exactly the one-event simulator semantics. -/
theorem invariants (trace : Trace start advance)
    {valid : δ → Prop} {grows : δ → δ → Prop} {post : Fin count → α → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (fresh : ∀ worker state, valid state → Safe valid grows (post worker) (.ofProgram (start worker)) state)
    (clock : ∀ elapsed state, valid state → valid (advance elapsed state) ∧ grows state (advance elapsed state))
    (initial : AllSafe valid grows post (trace.states 0)) :
    (∀ n, AllSafe valid grows post (trace.states n)) ∧
      ∀ before after, before ≤ after → grows (trace.states before).durable (trace.states after).durable := by
  have kept n : AllSafe valid grows post (trace.states n) := by
    induction n with
    | zero => exact initial
    | succ n ih => exact (step_safe refl trans start advance post fresh clock (trace.events n) ih (trace.execution n)).2
  refine ⟨kept, ?_⟩
  intro before after later
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
  induction offset with
  | zero => exact refl _
  | succ offset ih =>
    have edge := step_safe refl trans start advance post fresh clock (trace.events (before + offset))
      (kept _) (trace.execution _)
    exact trans (ih (by omega)) edge.1

/-- Every worker whose crashes eventually stop returns under weak fairness.
The result satisfies its existing safety contract; workflow success and fuel
adequacy are deliberately not assumptions of scheduler fairness. -/
theorem eventually_returns (trace : Trace start advance) (fair : trace.WeaklyFair)
    {valid : δ → Prop} {grows : δ → δ → Prop} {post : Fin count → α → δ → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (fresh : ∀ worker state, valid state → Safe valid grows (post worker) (.ofProgram (start worker)) state)
    (clock : ∀ elapsed state, valid state → valid (advance elapsed state) ∧ grows state (advance elapsed state))
    (initial : AllSafe valid grows post (trace.states 0))
    (worker : Fin count) (cut : Nat) (noCrash : trace.NoCrashesAfter worker cut) :
    ∃ later value, cut ≤ later ∧ (trace.states later).workers worker = .finished value ∧
      post worker value (trace.states later).durable := by
  obtain ⟨kept, growth⟩ := trace.invariants refl trans fresh clock initial
  exact trace.schedule.finishes (trace.schedule_fair fair) worker refl trans (fun n => (kept n).1) growth (fresh worker)
    cut ((kept cut).2 worker) (trace.schedule_noCrashes worker cut noCrash)

end Trace
end LeanCloud.Simulation
