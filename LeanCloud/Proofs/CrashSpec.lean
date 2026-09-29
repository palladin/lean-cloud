import LeanCloud.Proofs.Crash

/-! Compositional specifications for calls that may crash before or after an
atomic operation. Ordinary return and interruption have separate postconditions;
neither rolls back committed state. -/

namespace LeanCloud.Proofs.CrashRecovery
open CrashModel

/-- A call preserves its ordinary postcondition on return, or its interruption
postcondition on crash. Every crash consumes a fault entry. -/
def Triple (pre : δ → Prop) (action : M δ α)
    (post : α → δ → Prop) (stopped : δ → Prop) : Prop :=
  ∀ start, pre start.durable →
    let (result, final) := action.run start
    final.faults.script.length ≤ start.faults.script.length ∧
    match result with
    | .ok value => post value final.durable
    | .error _ => stopped final.durable ∧
        final.faults.script.length < start.faults.script.length

theorem Triple.pure (pre : δ → Prop) (value : α) :
    Triple pre (pure value) (fun result state => result = value ∧ pre state) stopped := by
  intro start valid
  exact ⟨Nat.le_refl _, rfl, valid⟩

theorem Triple.weaken {pre pre' : δ → Prop} {action : M δ α} {post post' stopped stopped'}
    (spec : Triple pre action post stopped)
    (before : ∀ state, pre' state → pre state)
    (returned : ∀ value state, post value state → post' value state)
    (interrupted : ∀ state, stopped state → stopped' state) :
    Triple pre' action post' stopped' := by
  intro start valid
  have observed := spec start (before _ valid)
  generalize execution : action.run start = run at *
  rcases run with ⟨result, final⟩
  refine ⟨observed.1, ?_⟩
  cases result with
  | ok value => exact returned _ _ observed.2
  | error crash => exact ⟨interrupted _ observed.2.1, observed.2.2⟩

theorem Triple.bind {pre : δ → Prop} {action : M δ α} {next : α → M δ β}
    {middle post stopped}
    (first : Triple pre action middle stopped)
    (rest : ∀ value, Triple (middle value) (next value) post stopped) :
    Triple pre (action >>= next) post stopped := by
  intro start valid
  have observed := first start valid
  rw [run_bind]
  generalize execution : action.run start = run at *
  rcases run with ⟨result, committed⟩
  cases result with
  | error crash => exact observed
  | ok value =>
    have later := rest value committed observed.2
    change let (result, final) := (next value).run committed
      final.faults.script.length ≤ start.faults.script.length ∧
      match result with
      | .ok value => post value final.durable
      | .error _ => stopped final.durable ∧
          final.faults.script.length < start.faults.script.length
    generalize execution : (next value).run committed = run at *
    rcases run with ⟨result, final⟩
    refine ⟨Nat.le_trans later.1 observed.1, ?_⟩
    cases result with
    | ok value => exact later.2
    | error crash => exact ⟨later.2.1, Nat.lt_of_lt_of_le later.2.2 observed.1⟩

/-- Independent specifications of the same execution hold together, including
when that execution stops after a committed operation. -/
theorem Triple.conjoin {pre₁ pre₂ : δ → Prop} {action : M δ α}
    {post₁ post₂ stopped₁ stopped₂}
    (first : Triple pre₁ action post₁ stopped₁)
    (second : Triple pre₂ action post₂ stopped₂) :
    Triple (fun state => pre₁ state ∧ pre₂ state) action
      (fun value state => post₁ value state ∧ post₂ value state)
      (fun state => stopped₁ state ∧ stopped₂ state) := by
  intro start valid
  have left := first start valid.1
  have right := second start valid.2
  generalize execution : action.run start = run at *
  obtain ⟨result, final⟩ := run
  refine ⟨left.1, ?_⟩
  cases result with
  | ok _ => exact ⟨left.2, right.2⟩
  | error _ => exact ⟨⟨left.2.1, right.2.1⟩, left.2.2⟩

/-- Attach a durable-state fact proved for every outcome of this actual call.
Fault accounting and the returned value still come from its specification. -/
theorem Triple.ensure {pre : δ → Prop} {action : M δ α} {post stopped} {invariant : δ → Prop}
    (spec : Triple pre action post stopped)
    (kept : ∀ start : State δ, pre start.durable → invariant (action.run start).2.durable) :
    Triple pre action (fun value state => post value state ∧ invariant state)
      (fun state => stopped state ∧ invariant state) := by
  intro start valid
  have safe := spec start valid
  have invariantNow := kept start valid
  generalize execution : action.run start = run at *
  obtain ⟨result, final⟩ := run
  refine ⟨safe.1, ?_⟩
  cases result with
  | ok _ => exact ⟨safe.2, invariantNow⟩
  | error _ => exact ⟨⟨safe.2.1, invariantNow⟩, safe.2.2⟩

theorem Triple.map {pre : δ → Prop} {action : M δ α} {post stopped}
    (spec : Triple pre action post stopped) (f : α → β) :
    Triple pre (f <$> action)
      (fun result state => ∃ value, result = f value ∧ post value state) stopped := by
  intro start valid
  have observed := spec start valid
  rw [run_map]
  generalize execution : action.run start = run at *
  rcases run with ⟨result, final⟩
  refine ⟨observed.1, ?_⟩
  cases result with
  | ok value => exact ⟨value, rfl, observed.2⟩
  | error crash => exact observed.2

theorem Triple.atomic (operation : δ → α × δ) {pre post stopped}
    (returned : ∀ state, pre state → post (operation state).1 (operation state).2)
    (before : ∀ state, pre state → stopped state)
    (after : ∀ state, pre state → stopped (operation state).2) :
    Triple pre (atomic operation) post stopped := by
  intro start valid
  have observed := atomic_observation operation start
  generalize execution : (CrashModel.atomic operation).run start = run at *
  rcases run with ⟨result, final⟩
  refine ⟨observed.1, ?_⟩
  cases result with
  | ok value =>
    rcases observed.2 with ⟨rfl, same⟩
    simpa [same] using returned start.durable valid
  | error crash =>
    refine ⟨?_, observed.2.1⟩
    rcases observed.2.2 with same | same
    · simpa [same] using before start.durable valid
    · simpa [same] using after start.durable valid

/-- Read-only computations observe a fixed durable state, while still permitting
a crash at any primitive read. Fault bookkeeping is deliberately not fixed. -/
def Reads (action : M δ α) (state : δ) (value : α) : Prop :=
  Triple (· = state) action (fun result final => result = value ∧ final = state) (· = state)

theorem Reads.pure (state : δ) (value : α) : Reads (pure value) state value :=
  Triple.pure _ _

theorem Reads.bind {action : M δ α} {next : α → M δ β} {state value result}
    (first : Reads action state value) (rest : Reads (next value) state result) :
    Reads (action >>= next) state result := by
  apply Triple.bind first
  intro returned
  intro start valid
  rcases valid with ⟨rfl, same⟩
  exact rest start same

theorem Reads.map {action : M δ α} {state value}
    (spec : Reads action state value) (f : α → β) : Reads (f <$> action) state (f value) := by
  exact (Triple.map spec f).weaken (fun _ h => h)
    (fun result final ⟨returned, equal, returnedEq, same⟩ =>
      ⟨equal.trans (congrArg f returnedEq), same⟩) (fun _ h => h)

theorem Reads.atomic (observe : δ → α) (state : δ) :
    Reads (atomic fun durable => (observe durable, durable)) state (observe state) := by
  apply Triple.atomic
  · intro final same; subst final; exact ⟨rfl, rfl⟩
  · exact fun _ h => h
  · exact fun _ h => h

end LeanCloud.Proofs.CrashRecovery
