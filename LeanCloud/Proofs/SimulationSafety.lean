import LeanCloud.Proofs.Simulation

/-! Safety of suspended computations under interference. A waiting operation and
a saved response must remain safe at every permitted extension of shared state.
This rule reasons about the actual simulator, including crashes and restarts. -/

namespace LeanCloud.Simulation
open LeanEff

/-- `grows` describes permitted interference; `valid` describes shared storage.
The responding case deliberately retains the old response while quantifying
over newer states. No assumption says that storage stayed unchanged. -/
inductive Safe (valid : δ → Prop) (grows : δ → δ → Prop) (post : α → δ → Prop) :
    Worker δ α → δ → Prop where
  | waiting {β : Type} {operation : δ → β × δ} {next : ArrsF (Atomic δ) β α} {state : δ}
      (commit : ∀ current, valid current → grows state current →
        valid (operation current).2 ∧ grows current (operation current).2)
      (safe : ∀ current, valid current → grows state current →
        Safe valid grows post (.responding (operation current).1 next) (operation current).2) :
      Safe valid grows post (.waiting operation next) state
  | responding {β : Type} {value : β} {next : ArrsF (Atomic δ) β α} {state : δ}
      (safe : ∀ current, valid current → grows state current →
        Safe valid grows post (.ofProgram (ArrsF.apply next value)) current) :
      Safe valid grows post (.responding value next) state
  | finished {value : α} {state : δ}
      (safe : ∀ current, valid current → grows state current → post value current) :
      Safe valid grows post (.finished value) state
  | stopped {state : δ} : Safe valid grows post .stopped state

/-- A finite prefix of a suspended worker reaches `goal`. Unlike `Safe`, this
may stop at an internal boundary: the rest of the worker need not return.
Global trace invariants supply validity and permitted interference. -/
inductive Reaches (valid : δ → Prop) (grows : δ → δ → Prop)
    (goal : Worker δ α → δ → Prop) : Worker δ α → δ → Prop where
  | arrived {worker state}
      (reached : ∀ current, valid current → grows state current → goal worker current) :
      Reaches valid grows goal worker state
  | waiting {β : Type} {operation : δ → β × δ} {next : ArrsF (Atomic δ) β α} {state : δ}
      (remaining : ∀ current, valid current → grows state current →
        Reaches valid grows goal (.responding (operation current).1 next) (operation current).2) :
      Reaches valid grows goal (.waiting operation next) state
  | responding {β : Type} {value : β} {next : ArrsF (Atomic δ) β α} {state : δ}
      (remaining : ∀ current, valid current → grows state current →
        Reaches valid grows goal (.ofProgram (ArrsF.apply next value)) current) :
      Reaches valid grows goal (.responding value next) state

variable {valid : δ → Prop} {grows : δ → δ → Prop} {post : α → δ → Prop}

theorem Reaches.weaken {goal goal' : Worker δ α → δ → Prop} {worker : Worker δ α} {state : δ}
    (progress : Reaches valid grows goal worker state)
    (implies : ∀ worker current, valid current → goal worker current → goal' worker current) :
    Reaches valid grows goal' worker state := by
  induction progress with
  | arrived reached => exact .arrived fun current kept growth => implies _ current kept (reached current kept growth)
  | waiting remaining ih => exact .waiting ih
  | responding remaining ih => exact .responding ih

theorem Safe.reaches_return {worker : Worker δ α} {state : δ}
    (safe : Safe valid grows post worker state) (running : worker ≠ .stopped) :
    Reaches valid grows (fun worker current => ∃ value, worker = .finished value ∧ post value current) worker state := by
  induction safe with
  | waiting commit next ih => exact .waiting fun current kept growth => ih current kept growth (by simp)
  | responding next ih =>
    apply Reaches.responding
    intro current kept growth
    apply ih current kept growth
    cases ArrsF.apply _ _ with
    | pure value => simp [Worker.ofProgram]
    | impure operation next => cases operation; simp [Worker.ofProgram]
  | finished done => exact .arrived fun current kept growth => ⟨_, rfl, done current kept growth⟩
  | stopped => exact False.elim (running rfl)

theorem Safe.mono {worker : Worker δ α} {before after : δ}
    (safe : Safe valid grows post worker before)
    (trans : ∀ {a b c : δ}, grows a b → grows b c → grows a c)
    (growth : grows before after) :
    Safe valid grows post worker after := by
  cases safe with
  | waiting commit next =>
    exact .waiting
      (fun current h later => commit current h (trans growth later))
      (fun current h later => next current h (trans growth later))
  | responding next => exact .responding fun current h later => next current h (trans growth later)
  | finished done => exact .finished fun current h later => done current h (trans growth later)
  | stopped => exact .stopped

/-- Add an invariant that every permitted state extension preserves. -/
theorem Safe.strengthen {worker : Worker δ α} {state : δ}
    (safe : Safe valid grows post worker state) (stronger : δ → Prop)
    (implies : ∀ state, stronger state → valid state)
    (preserved : ∀ before after, stronger before → valid after → grows before after → stronger after) :
    Safe stronger grows post worker state := by
  induction safe with
  | waiting commit next ih =>
    apply Safe.waiting
    · intro current kept growth
      obtain ⟨valid, later⟩ := commit current (implies current kept) growth
      exact ⟨preserved current _ kept valid later, later⟩
    · intro current kept growth
      exact ih current (implies current kept) growth
  | responding next ih =>
    exact .responding fun current kept growth => ih current (implies current kept) growth
  | finished done =>
    exact .finished fun current kept growth => done current (implies current kept) growth
  | stopped => exact .stopped

/-- Derive a caller's result contract from the existing one. -/
theorem Safe.weaken {worker : Worker δ α} {state : δ}
    (safe : Safe valid grows post worker state) (post' : α → δ → Prop)
    (implies : ∀ value current, valid current → post value current → post' value current) :
    Safe valid grows post' worker state := by
  induction safe with
  | waiting commit next ih => exact .waiting commit ih
  | responding next ih => exact .responding ih
  | finished done =>
    exact .finished fun current kept growth => implies _ current kept (done current kept growth)
  | stopped => exact .stopped

/-- Retain a lower bound while composing calls that preserve shared records. -/
theorem Safe.remember {worker : Worker δ α} {state : δ}
    (safe : Safe valid grows post worker state)
    (trans : ∀ {a b c : δ}, grows a b → grows b c → grows a c)
    (before : δ) (prior : grows before state) :
    Safe valid grows (fun value final => grows before final ∧ post value final) worker state := by
  induction safe with
  | waiting commit next ih =>
    apply Safe.waiting commit
    intro current kept growth
    exact ih current kept growth (trans prior (trans growth (commit current kept growth).2))
  | responding next ih =>
    exact .responding fun current kept growth => ih current kept growth (trans prior growth)
  | finished done =>
    exact .finished fun current kept growth => ⟨trans prior growth, done current kept growth⟩
  | stopped => exact .stopped

/-- A running computation must commit its first operation before it can
return. Keep any stable fact established by that commit in its postcondition. -/
theorem Safe.after_commit {operation : δ → β × δ} {next : ArrsF (Atomic δ) β α} {state : δ}
    (safe : Safe valid grows post (.waiting operation next) state)
    (refl : ∀ current, grows current current)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (property : δ → Prop)
    (established : ∀ current, valid current → grows state current → property (operation current).2)
    (stable : ∀ before after, property before → grows before after → property after) :
    Safe valid grows (fun value final => post value final ∧ property final) (.waiting operation next) state := by
  cases safe with
  | waiting commit remaining =>
    apply Safe.waiting commit
    intro current kept growth
    apply ((remaining current kept growth).remember trans (operation current).2 (refl _)).weaken
    intro value final finalValid result
    exact ⟨result.2, stable _ _ (established current kept growth) result.1⟩

/-- Combine two proofs of the same suspended computation. Each sees only the
invariant and interference facts it needs; both postconditions are retained. -/
theorem Safe.combine {leftValid rightValid valid : δ → Prop}
    {leftGrows rightGrows grows : δ → δ → Prop} {leftPost rightPost : α → δ → Prop}
    {worker : Worker δ α} {state : δ}
    (left : Safe leftValid leftGrows leftPost worker state)
    (right : Safe rightValid rightGrows rightPost worker state)
    (splitValid : ∀ current, valid current → leftValid current ∧ rightValid current)
    (joinValid : ∀ current, leftValid current → rightValid current → valid current)
    (splitGrowth : ∀ before after, grows before after → leftGrows before after ∧ rightGrows before after)
    (joinGrowth : ∀ before after, leftGrows before after → rightGrows before after → grows before after) :
    Safe valid grows (fun value final => leftPost value final ∧ rightPost value final) worker state := by
  induction left with
  | waiting commit next ih =>
    cases right with
    | waiting otherCommit otherNext =>
      apply Safe.waiting
      · intro current kept growth
        have first := commit current (splitValid current kept).1 (splitGrowth _ _ growth).1
        have second := otherCommit current (splitValid current kept).2 (splitGrowth _ _ growth).2
        exact ⟨joinValid _ first.1 second.1, joinGrowth _ _ first.2 second.2⟩
      · intro current kept growth
        exact ih current (splitValid current kept).1 (splitGrowth _ _ growth).1
          (otherNext current (splitValid current kept).2 (splitGrowth _ _ growth).2)
  | responding next ih =>
    cases right with
    | responding otherNext =>
      exact .responding fun current kept growth => ih current (splitValid current kept).1 (splitGrowth _ _ growth).1
        (otherNext current (splitValid current kept).2 (splitGrowth _ _ growth).2)
  | finished done =>
    cases right with
    | finished otherDone =>
      exact .finished fun current kept growth =>
        ⟨done current (splitValid current kept).1 (splitGrowth _ _ growth).1,
          otherDone current (splitValid current kept).2 (splitGrowth _ _ growth).2⟩
  | stopped => exact .stopped

def AllSafe (valid : δ → Prop) (grows : δ → δ → Prop)
    (post : Fin count → α → δ → Prop) (state : State δ α count) : Prop :=
  valid state.durable ∧ ∀ worker, Safe valid grows (post worker) (state.workers worker) state.durable

theorem AllSafe.update {post : Fin count → α → δ → Prop} {state : State δ α count}
    (safe : AllSafe valid grows post state)
    (trans : ∀ {a b c : δ}, grows a b → grows b c → grows a c)
    (worker : Fin count) (next : Worker δ α) (durable : δ)
    (kept : valid durable) (growth : grows state.durable durable)
    (localSafe : Safe valid grows (post worker) next durable) :
    AllSafe valid grows post { state.setWorker worker next with durable } := by
  refine ⟨kept, fun other => ?_⟩
  by_cases same : other = worker
  · subst other
    simpa only [State.setWorker_same] using localSafe
  · simpa only [State.setWorker_other state worker other next same] using
      (safe.2 other).mono trans growth

/-- One event preserves all workers' obligations and grows the shared state.
Restart safety is checked at the current durable state, not just at startup. -/
theorem step_safe (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (start : Fin count → SimM δ α) (advance : Nat → δ → δ)
    (post : Fin count → α → δ → Prop)
    (fresh : ∀ worker state, valid state →
      Safe valid grows (post worker) (.ofProgram (start worker)) state)
    (clock : ∀ elapsed state, valid state →
      valid (advance elapsed state) ∧ grows state (advance elapsed state))
    (event : Event count) {state final : State δ α count}
    (safe : AllSafe valid grows post state)
    (executed : step start advance event state = .ok final) :
    grows state.durable final.durable ∧ AllSafe valid grows post final := by
  cases event with
  | commit worker =>
    have localSafe := safe.2 worker
    cases observed : state.workers worker <;> simp only [step, observed] at executed
    case waiting operation next =>
      rw [observed] at localSafe
      cases localSafe with
      | waiting commit permitted =>
        obtain ⟨kept, growth⟩ := commit state.durable safe.1 (refl _)
        have remaining := permitted state.durable safe.1 (refl _)
        cases executed
        exact ⟨growth, safe.update trans worker _ _ kept growth remaining⟩
    all_goals cases executed
  | resume worker =>
    have localSafe := safe.2 worker
    cases observed : state.workers worker <;> simp only [step, observed] at executed
    case responding value next =>
      rw [observed] at localSafe
      cases localSafe with
      | responding permitted =>
        cases executed
        exact ⟨refl _, safe.update trans worker _ _ safe.1 (refl _)
          (permitted state.durable safe.1 (refl _))⟩
    all_goals cases executed
  | crash worker =>
    cases observed : state.workers worker <;> simp only [step, observed] at executed
    all_goals cases executed
    all_goals exact ⟨refl _, safe.update trans worker _ _ safe.1 (refl _) .stopped⟩
  | restart worker =>
    cases observed : state.workers worker <;> simp only [step, observed] at executed
    all_goals cases executed
    exact ⟨refl _, safe.update trans worker _ _ safe.1 (refl _) (fresh worker _ safe.1)⟩
  | advanceTime elapsed =>
    cases executed
    obtain ⟨kept, growth⟩ := clock elapsed state.durable safe.1
    exact ⟨growth, kept, fun worker => (safe.2 worker).mono trans growth⟩

/-- Every finite legal schedule preserves safety. No fairness or termination
assumption is needed; unfinished and crashed workers are permitted. -/
theorem run_safe (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (start : Fin count → SimM δ α) (advance : Nat → δ → δ)
    (post : Fin count → α → δ → Prop)
    (fresh : ∀ worker state, valid state →
      Safe valid grows (post worker) (.ofProgram (start worker)) state)
    (clock : ∀ elapsed state, valid state →
      valid (advance elapsed state) ∧ grows state (advance elapsed state))
    (events : List (Event count)) {state final : State δ α count}
    (safe : AllSafe valid grows post state)
    (executed : run start advance events state = .ok final) :
    grows state.durable final.durable ∧ AllSafe valid grows post final := by
  induction events generalizing state with
  | nil =>
    cases executed
    exact ⟨refl _, safe⟩
  | cons event events ih =>
    change (step start advance event state >>= fun middle => run start advance events middle) = .ok final at executed
    cases first : step start advance event state with
    | error error => simp [first, bind, Except.bind] at executed
    | ok middle =>
      obtain ⟨growth, remaining⟩ := step_safe refl trans start advance post fresh clock event safe first
      have tail : run start advance events middle = .ok final := by
        simpa only [first, bind, Except.bind] using executed
      obtain ⟨later, finished⟩ := ih remaining tail
      exact ⟨trans growth later, finished⟩

theorem Safe.returned (refl : ∀ state, grows state state) {worker : Worker δ α} {state : δ}
    (safe : Safe valid grows post worker state) (kept : valid state)
    (returned : worker.outcome? = some value) : post value state := by
  cases safe <;> simp only [Worker.outcome?] at returned
  case finished actual done =>
    cases returned
    exact done state kept (refl state)
  all_goals cases returned

end LeanCloud.Simulation
