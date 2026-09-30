import LeanCloud.Proofs.SimulationHistory
import LeanCloud.Proofs.SimulationLoop

/-! Recording the concrete repeated execution preserves its events and results.
Repetition adds no durable snapshot, just like ordinary reply delivery. This
connects publication certificates to actual boundaries of the unrecorded trace. -/

namespace LeanCloud.Simulation.History

def repeatedPastAfter (event : Repeated.Event count) (source : State δ α count) (past : List δ) : List δ :=
  match event with
  | .ordinary event => pastAfter event source past
  | .repeatIteration _ => past

theorem repeated_step_correspondence (start : Fin count → SimM δ α) (clock : Nat → δ → δ) (again : α → Bool)
    (event : Repeated.Event count) (source : State δ α count) (past : List δ) :
    Repeated.step (fun index => program (start index)) (advance clock) again event (state past source) =
      (Repeated.step start clock again event source).map (state (repeatedPastAfter event source past)) := by
  cases event with
  | ordinary event =>
    simp only [Repeated.step, repeatedPastAfter, step_correspondence]
    cases Simulation.step start clock event source <;> rfl
  | repeatIteration index =>
    cases seen : source.workers index <;>
      simp only [Repeated.step, state, seen, worker, repeatedPastAfter, Except.map]
    case finished value =>
      split
      next allowed =>
        rw [← worker_program]
        exact congrArg Except.ok (state_setWorker past source index (.ofProgram (start index))).symm
      next refused => rfl

/-- Any finite concrete schedule lifts, retaining the same errors, outcomes,
saved replies and repeat eligibility. Only physical commits and time add history. -/
theorem repeated_run_correspondence (start : Fin count → SimM δ α) (clock : Nat → δ → δ) (again : α → Bool)
    (events : List (Repeated.Event count)) (source final : State δ α count) (past : List δ)
    (executed : Repeated.run start clock again events source = .ok final) :
    ∃ history, Repeated.run (fun index => program (start index)) (advance clock) again events (state past source) =
      .ok (state history final) ∧ history.length ≤ past.length + events.length := by
  induction events generalizing source past with
  | nil => cases executed; exact ⟨past, rfl, Nat.le_refl _⟩
  | cons event events ih =>
    change (Repeated.step start clock again event source >>= fun middle =>
      Repeated.run start clock again events middle) = _ at executed
    cases first : Repeated.step start clock again event source with
    | error error => simp [first, bind, Except.bind] at executed
    | ok middle =>
      obtain ⟨history, tail, bound⟩ := ih middle (repeatedPastAfter event source past)
        (by simpa only [first, bind, Except.bind] using executed)
      refine ⟨history, ?_, ?_⟩
      · change (Repeated.step _ _ _ event _ >>= fun middle => Repeated.run _ _ _ events middle) = _
        rw [repeated_step_correspondence, first]
        exact tail
      · cases event with
        | repeatIteration index => simp only [repeatedPastAfter, List.length_cons] at bound ⊢; omega
        | ordinary event => cases event <;> simp only [repeatedPastAfter, pastAfter, List.length_cons] at bound ⊢ <;> omega

private def repeatedTracePast {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}
    (source : Repeated.Trace start clock again) : Nat → List δ
  | 0 => []
  | n + 1 => repeatedPastAfter (source.events n) (source.states n) (repeatedTracePast source n)

def repeatedTrace {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}
    (source : Repeated.Trace start clock again) :
    Repeated.Trace (fun index => program (start index)) (advance clock) again where
  states n := state (repeatedTracePast source n) (source.states n)
  events := source.events
  execution n := by
    rw [repeated_step_correspondence, source.execution]
    rfl

theorem repeated_trace_current {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}
    (source : Repeated.Trace start clock again) (n : Nat) :
    ((repeatedTrace source).states n).durable.current = (source.states n).durable := rfl

theorem repeated_trace_outcome {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}
    (source : Repeated.Trace start clock again) (n : Nat) (index : Fin count) :
    (((repeatedTrace source).states n).workers index).outcome? = ((source.states n).workers index).outcome? := worker_outcome _

private theorem worker_finished {source : Worker δ α} {value : α} :
    worker source = .finished value ↔ source = .finished value := by
  cases source <;> simp [worker]

theorem repeated_trace_fair {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}
    (source : Repeated.Trace start clock again) (fair : source.WeaklyFair) : (repeatedTrace source).WeaklyFair := by
  constructor
  · constructor
    · intro index n enabled
      exact fair.workers.commit index n (fun later after => by
        simpa only [Repeated.Trace.schedule, repeatedTrace, state, worker_phase] using enabled later after)
    · intro index n enabled
      exact fair.workers.resume index n (fun later after => by
        simpa only [Repeated.Trace.schedule, repeatedTrace, state, worker_phase] using enabled later after)
    · intro index n enabled
      exact fair.workers.restart index n (fun later after => by
        simpa only [Repeated.Trace.schedule, repeatedTrace, state, worker_phase] using enabled later after)
  · intro index n enabled
    apply fair.iterations index n
    intro later after
    obtain ⟨value, held, repeatable⟩ := enabled later after
    exact ⟨value, worker_finished.mp held, repeatable⟩

theorem repeated_trace_noCrashes {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}
    (source : Repeated.Trace start clock again) (index : Fin count) (cut : Nat)
    (noCrash : source.NoCrashesAfter index cut) : (repeatedTrace source).NoCrashesAfter index cut := noCrash

theorem repeated_trace_initial {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}
    (source : Repeated.Trace start clock again) (initial : δ)
    (initialized : source.states 0 = State.initial initial start) :
    (repeatedTrace source).states 0 = State.initial ⟨initial, []⟩ (fun index => program (start index)) := by
  change state [] (source.states 0) = _
  rw [initialized]
  apply (State.mk.injEq ..).mpr
  refine ⟨rfl, ?_⟩
  funext index
  exact worker_program _

theorem repeated_trace_timeline {start : Fin count → SimM δ α} {clock : Nat → δ → δ} {again : α → Bool}
    (source : Repeated.Trace start clock again) : Timeline (fun n => ((repeatedTrace source).states n).durable) := by
  refine ⟨rfl, ?_⟩
  intro n
  cases event : source.events n with
  | repeatIteration index =>
    left
    have durable := (source.schedule.administrative n (by simp [Repeated.Trace.schedule, event])).1
    simp only [repeatedTrace, state, repeatedTracePast, event, repeatedPastAfter]
    exact congrArg (fun current => Store.mk current (repeatedTracePast source n)) durable
  | ordinary action =>
    have executed := source.schedule.execution n action (by simp [Repeated.Trace.schedule, event])
    change Simulation.step start clock action (source.states n) = .ok (source.states (n + 1)) at executed
    cases action with
    | commit index | advanceTime elapsed =>
      right
      simp only [repeatedTrace, state, repeatedTracePast, event, repeatedPastAfter, pastAfter, Store.states]
    | resume index | crash index | restart index =>
      left
      cases seen : (source.states n).workers index <;> simp only [Simulation.step, seen] at executed
      all_goals try { cases executed }
      all_goals
        have durable := congrArg State.durable (Except.ok.inj executed)
        simp only [repeatedTrace, state, repeatedTracePast, event, repeatedPastAfter, pastAfter]
        exact congrArg (fun current => Store.mk current (repeatedTracePast source n)) durable.symm

end LeanCloud.Simulation.History
