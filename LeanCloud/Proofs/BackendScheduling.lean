import LeanCloud.Proofs.BackendTraceSafety
import LeanCloud.Proofs.SimulationSchedule

namespace LeanCloud.Backend.Execution
open LeanEff

theorem activate_other {state : State α} {owner : Owner} {program : M α} {worker : Nat}
    (different : owner.worker ≠ worker) :
    (activate owner program state).workers[worker]? = state.workers[worker]? := by
  cases program <;> simp [activate, different]

theorem activate_old_call {state : State α} {owner : Owner} {program : M α} {id : Nat}
    (inside : id < state.calls.size) :
    (activate owner program state).calls[id]? = state.calls[id]? := by
  cases program <;> simp [activate, Array.getElem?_push, Nat.ne_of_lt inside]

theorem owns_iff (owner : Owner) (id : Nat) (state : State α) :
    owns owner id state = true ↔ state.workers[owner.worker]? = some ⟨owner.attempt, .waiting id⟩ := by
  simp only [owns]
  split <;> simp_all

def Waiting (owner : Owner) (id : Nat) (operation : Request β) (next : ArrsF Request β α)
    (state : State α) : Prop :=
  state.workers[owner.worker]? = some ⟨owner.attempt, .waiting id⟩ ∧
    state.calls[id]? = some (.pending owner operation (some next))

def Responds (owner : Owner) (id : Nat) (operation : Request β) (value : β)
    (next : ArrsF Request β α) (state : State α) : Prop :=
  state.workers[owner.worker]? = some ⟨owner.attempt, .waiting id⟩ ∧
    state.calls[id]? = some (.committed owner operation value (some next))

private theorem reply_other {programs : Array (M α)} {before after : State α}
    {id other : Nat} {owner : Owner} {call : Call α}
    (waiting : before.workers[owner.worker]? = some ⟨owner.attempt, .waiting id⟩)
    (held : before.calls[id]? = some call) (different : other ≠ id)
    (executed : step programs (.reply other) before = .ok after) :
    after.workers[owner.worker]? = before.workers[owner.worker]? ∧ after.calls[id]? = some call := by
  simp only [step] at executed
  split at executed <;> try contradiction
  rename_i β caller operation value next stored
  split at executed
  · cases executed
    exact ⟨rfl, by simpa [Array.getElem?_setIfInBounds, different] using held⟩
  · rename_i rest
    split at executed <;> try contradiction
    rename_i ownsCall
    have active := (owns_iff caller other before).mp ownsCall
    have apart : caller.worker ≠ owner.worker := by
      intro same
      rw [same, waiting] at active
      have equality := congrArg Worker.status (Option.some.inj active)
      exact different (Status.waiting.inj equality).symm
    cases executed
    constructor
    · exact activate_other apart
    · rw [activate_old_call (by simpa using (Array.getElem?_eq_some_iff.mp held).choose)]
      simpa [Array.getElem?_setIfInBounds, different] using held

private theorem restart_other {programs : Array (M α)} {before after : State α}
    {id other : Nat} {owner : Owner} {call : Call α}
    (waiting : before.workers[owner.worker]? = some ⟨owner.attempt, .waiting id⟩)
    (held : before.calls[id]? = some call)
    (executed : step programs (.restart other) before = .ok after) :
    after.workers[owner.worker]? = before.workers[owner.worker]? ∧ after.calls[id]? = some call := by
  simp only [step] at executed
  split at executed <;> try contradiction
  rename_i worker stored
  split at executed <;> try contradiction
  split at executed <;> try contradiction
  rename_i stopped
  have apart : other ≠ owner.worker := by
    intro same
    rw [same, waiting] at stored
    cases stored
    cases stopped
  cases executed
  exact ⟨activate_other apart, (activate_old_call (Array.getElem?_eq_some_iff.mp held).choose).trans held⟩

theorem Waiting.unchanged {programs : Array (M α)} {before after : State α}
    {owner : Owner} {id : Nat} {operation : Request β} {next : ArrsF Request β α} {action : Action}
    (held : Waiting owner id operation next before) (executed : Transition programs action before after)
    (noCommit : action ≠ .commit id) (noCrash : action ≠ .crash owner.worker) :
    Waiting owner id operation next after := by
  cases executed with
  | @commit β _ other caller operation rest value services issued lawful =>
    have different : other ≠ id := by intro same; subst other; exact noCommit rfl
    exact ⟨held.1, by simpa [Array.getElem?_setIfInBounds, different] using held.2⟩
  | @reply other _ _ executed =>
    have different : other ≠ id := by
      intro same
      subst other
      simp [step, held.2] at executed
    obtain ⟨worker, call⟩ := reply_other held.1 held.2 different executed
    exact ⟨worker.trans held.1, call⟩
  | @restart other _ _ executed =>
    obtain ⟨worker, call⟩ := restart_other held.1 held.2 executed
    exact ⟨worker.trans held.1, call⟩
  | @crash other _ _ executed =>
    have different : other ≠ owner.worker := by intro same; subst other; exact noCrash rfl
    simp only [step] at executed
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    cases executed
    constructor
    · simpa [Array.getElem?_setIfInBounds, different] using held.1
    · simp only [Array.getElem?_map, held.2, Option.map_some, Call.orphan]
      simp [BEq.beq, instBEqOwner.beq, Ne.symm different]

theorem Responds.unchanged {programs : Array (M α)} {before after : State α}
    {owner : Owner} {id : Nat} {operation : Request β} {value : β} {next : ArrsF Request β α} {action : Action}
    (held : Responds owner id operation value next before) (executed : Transition programs action before after)
    (noReply : action ≠ .reply id) (noCrash : action ≠ .crash owner.worker) :
    Responds owner id operation value next after := by
  cases executed with
  | @commit β _ other caller operation rest value services issued lawful =>
    have different : other ≠ id := by
      intro same
      subst other
      rw [held.2] at issued
      cases issued
    exact ⟨held.1, by simpa [Array.getElem?_setIfInBounds, different] using held.2⟩
  | @reply other _ _ executed =>
    have different : other ≠ id := by intro same; subst other; exact noReply rfl
    obtain ⟨worker, call⟩ := reply_other held.1 held.2 different executed
    exact ⟨worker.trans held.1, call⟩
  | @restart other _ _ executed =>
    obtain ⟨worker, call⟩ := restart_other held.1 held.2 executed
    exact ⟨worker.trans held.1, call⟩
  | @crash other _ _ executed =>
    have different : other ≠ owner.worker := by intro same; subst other; exact noCrash rfl
    simp only [step] at executed
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    cases executed
    constructor
    · simpa [Array.getElem?_setIfInBounds, different] using held.1
    · simp only [Array.getElem?_map, held.2, Option.map_some, Call.orphan]
      simp [BEq.beq, instBEqOwner.beq, Ne.symm different]

theorem Waiting.committed {programs : Array (M α)} {before after : State α}
    {owner : Owner} {id : Nat} {operation : Request β} {next : ArrsF Request β α}
    (held : Waiting owner id operation next before)
    (executed : Transition programs (.commit id) before after) :
    ∃ value, Responds owner id operation value next after ∧
      Commits before.services operation value after.services := by
  cases executed with
  | commit issued lawful =>
    rw [held.2] at issued
    cases issued
    exact ⟨_, ⟨held.1, by simp [(Array.getElem?_eq_some_iff.mp held.2).choose]⟩, lawful⟩

theorem Responds.replied {programs : Array (M α)} {before after : State α}
    {owner : Owner} {id : Nat} {operation : Request β} {value : β} {next : ArrsF Request β α}
    (held : Responds owner id operation value next before)
    (executed : Transition programs (.reply id) before after) :
    after = activate owner (ArrsF.apply next value) {before with calls := before.calls.setIfInBounds id .retired} := by
  cases executed with
  | reply executed =>
    have owns := (owns_iff owner id before).mpr held.1
    simpa only [step, held.2, owns, Bool.true_eq, ↓reduceIte, pure, Except.pure, Except.ok.injEq] using executed.symm

theorem Transition.commit_reply {programs : Array (M α)} {before after : State α}
    {owner : Owner} {id : Nat} {operation : Request β} {value : β} {next : Option (ArrsF Request β α)}
    (executed : Transition programs (.commit id) before after)
    (stored : after.calls[id]? = some (.committed owner operation value next)) :
    before.calls[id]? = some (.pending owner operation next) ∧
      Commits before.services operation value after.services := by
  cases executed with
  | commit issued lawful =>
    have inside := (Array.getElem?_eq_some_iff.mp issued).choose
    simp only [Array.getElem?_setIfInBounds_self, inside, ↓reduceIte] at stored
    cases stored
    exact ⟨issued, lawful⟩

/-- Proof-only iteration boundaries may activate a finished worker. They
preserve service state, every active worker and every existing service call. -/
structure Schedule (programs : Array (M α)) where
  states : Nat → State α
  events : Nat → Option Action
  execution : ∀ time action, events time = some action →
    Transition programs action (states time) (states (time + 1))
  administrative : ∀ time, events time = none →
    (states (time + 1)).services = (states time).services ∧
    (∀ (worker attempt : Nat) (status : Status α), (states time).workers[worker]? = some ⟨attempt, status⟩ →
      (∀ value, status ≠ .finished value) →
      (states (time + 1)).workers[worker]? = some ⟨attempt, status⟩) ∧
    ∀ (id : Nat) call, (states time).calls[id]? = some call →
      (states (time + 1)).calls[id]? = some call

theorem Transition.quiet_worker {programs : Array (M α)} {before after : State α} {worker attempt status action}
    (held : before.workers[worker]? = some ⟨attempt, status⟩)
    (quiet : ∀ id, status ≠ .waiting id) (noRestart : action ≠ .restart worker)
    (executed : Transition programs action before after) :
    after.workers[worker]? = some ⟨attempt, status⟩ := by
  cases executed with
  | commit issued lawful => exact held
  | @reply id _ _ executed =>
    simp only [step] at executed
    split at executed <;> try contradiction
    rename_i β owner operation value next stored
    split at executed
    · cases executed; exact held
    · split at executed <;> try contradiction
      rename_i owns
      have waiting := (owns_iff owner id before).mp owns
      have different : owner.worker ≠ worker := by
        intro same
        rw [same, held] at waiting
        exact quiet id (congrArg Worker.status (Option.some.inj waiting))
      cases executed
      exact (activate_other different).trans held
  | @restart other _ _ executed =>
    have different : other ≠ worker := by intro same; subst other; exact noRestart rfl
    simp only [step] at executed
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    cases executed
    exact (activate_other different).trans held
  | @crash other _ _ executed =>
    simp only [step] at executed
    split at executed <;> try contradiction
    rename_i current stored
    split at executed <;> try contradiction
    rename_i id waiting
    have different : other ≠ worker := by
      intro same
      rw [same, held] at stored
      cases stored
      exact quiet id waiting
    cases executed
    simpa [Array.getElem?_setIfInBounds, different] using held

namespace Schedule
variable {programs : Array (M α)}

structure WeaklyFair (trace : Schedule programs) : Prop where
  commit : ∀ id cut, (∀ n, cut ≤ n → Pending (trace.states n) id) →
    ∃ n, cut ≤ n ∧ trace.events n = some (.commit id)
  reply : ∀ id cut, (∀ n, cut ≤ n → Responding (trace.states n) id) →
    ∃ n, cut ≤ n ∧ trace.events n = some (.reply id)
  restart : ∀ worker cut, (∀ n, cut ≤ n → Stopped (trace.states n) worker) →
    ∃ n, cut ≤ n ∧ trace.events n = some (.restart worker)

def NoCrashesAfter (trace : Schedule programs) (worker cut : Nat) : Prop :=
  ∀ n, cut ≤ n → trace.events n ≠ some (.crash worker)

theorem eventually_restart (trace : Schedule programs) (fair : trace.WeaklyFair) {worker attempt time}
    (held : (trace.states time).workers[worker]? = some ⟨attempt, .stopped⟩) :
    ∃ later, time ≤ later ∧ (trace.states later).workers[worker]? = some ⟨attempt, .stopped⟩ ∧
      trace.events later = some (.restart worker) := by
  apply Simulation.first_event (fun n => (trace.states n).workers[worker]?) trace.events time _
    (some (.restart worker)) held
  · intro same
    exact fair.restart worker time (fun n later => ⟨attempt, same n later⟩)
  · intro n later present absent
    cases event : trace.events n with
    | none => exact (trace.administrative n event).2.1 worker attempt .stopped present (by intro value same; cases same)
    | some action =>
      exact Transition.quiet_worker present (by intro id same; cases same)
        (fun same => absent (event.trans (congrArg some same))) (trace.execution n action event)

theorem waiting_unchanged (trace : Schedule programs) {time owner id}
    {operation : Request β} {next : ArrsF Request β α}
    (held : Waiting owner id operation next (trace.states time))
    (absent : trace.events time ≠ some (.commit id)) (noCrash : trace.events time ≠ some (.crash owner.worker)) :
    Waiting owner id operation next (trace.states (time + 1)) := by
  cases event : trace.events time with
  | none =>
    have kept := trace.administrative time event
    exact ⟨kept.2.1 _ _ _ held.1 (by intro value same; cases same), kept.2.2 _ _ held.2⟩
  | some action =>
    exact held.unchanged (trace.execution time action event)
      (fun same => absent (event.trans (congrArg some same)))
      (fun same => noCrash (event.trans (congrArg some same)))

theorem responding_unchanged (trace : Schedule programs) {time owner id}
    {operation : Request β} {value : β} {next : ArrsF Request β α}
    (held : Responds owner id operation value next (trace.states time))
    (absent : trace.events time ≠ some (.reply id)) (noCrash : trace.events time ≠ some (.crash owner.worker)) :
    Responds owner id operation value next (trace.states (time + 1)) := by
  cases event : trace.events time with
  | none =>
    have kept := trace.administrative time event
    exact ⟨kept.2.1 _ _ _ held.1 (by intro value same; cases same), kept.2.2 _ _ held.2⟩
  | some action =>
    exact held.unchanged (trace.execution time action event)
      (fun same => absent (event.trans (congrArg some same)))
      (fun same => noCrash (event.trans (congrArg some same)))

theorem eventually_commit (trace : Schedule programs) (fair : trace.WeaklyFair) {owner id time}
    {operation : Request β} {next : ArrsF Request β α}
    (held : Waiting owner id operation next (trace.states time))
    (noCrash : trace.NoCrashesAfter owner.worker time) :
    ∃ later, time ≤ later ∧ Waiting owner id operation next (trace.states later) ∧
      trace.events later = some (.commit id) := by
  classical
  obtain ⟨later, after, present, event⟩ := Simulation.first_event
    (fun n => Waiting owner id operation next (trace.states n)) trace.events time True
    (some (.commit id)) (propext (iff_true_intro held))
    (fun all => fair.commit id time (by
      intro n after
      have now : Waiting owner id operation next (trace.states n) := (all n after).mpr trivial
      exact ⟨_, owner, operation, next, now.2⟩))
    (by
      intro n after now absent
      exact propext (iff_true_intro (trace.waiting_unchanged (now.mpr trivial) absent (noCrash n after))))
  exact ⟨later, after, present.mpr trivial, event⟩

theorem eventually_reply (trace : Schedule programs) (fair : trace.WeaklyFair) {owner id time}
    {operation : Request β} {value : β} {next : ArrsF Request β α}
    (held : Responds owner id operation value next (trace.states time))
    (noCrash : trace.NoCrashesAfter owner.worker time) :
    ∃ later, time ≤ later ∧ Responds owner id operation value next (trace.states later) ∧
      trace.events later = some (.reply id) := by
  classical
  obtain ⟨later, after, present, event⟩ := Simulation.first_event
    (fun n => Responds owner id operation value next (trace.states n)) trace.events time True
    (some (.reply id)) (propext (iff_true_intro held))
    (fun all => fair.reply id time (by
      intro n after
      have now : Responds owner id operation value next (trace.states n) := (all n after).mpr trivial
      exact ⟨_, owner, operation, value, next, now.2⟩))
    (by
      intro n after now absent
      exact propext (iff_true_intro (trace.responding_unchanged (now.mpr trivial) absent (noCrash n after))))
  exact ⟨later, after, present.mpr trivial, event⟩

end Schedule
end LeanCloud.Backend.Execution
