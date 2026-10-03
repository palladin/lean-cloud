import LeanCloud.Proofs.BackendRepeated

namespace LeanCloud.Backend.Execution
open LeanEff

def Call.rank : Call α → Nat
  | .pending .. => 0
  | .committed .. => 1
  | .retired => 2

theorem Call.rank_le (call : Call α) : call.rank ≤ 2 := by cases call <;> simp [Call.rank]

theorem Call.rank_orphan (call : Call α) (owner : Owner) : (call.orphan owner).rank = call.rank := by
  cases call <;> rfl

structure CallsGrow (before after : State α) : Prop where
  size : before.calls.size ≤ after.calls.size
  calls : ∀ (id : Nat) call, before.calls[id]? = some call →
    ∃ current, after.calls[id]? = some current ∧ call.rank ≤ current.rank

theorem CallsGrow.refl (state : State α) : CallsGrow state state := ⟨Nat.le_refl _, fun _ call held => ⟨call, held, Nat.le_refl _⟩⟩

theorem CallsGrow.trans {first middle last : State α} (a : CallsGrow first middle) (b : CallsGrow middle last) :
    CallsGrow first last := by
  refine ⟨Nat.le_trans a.size b.size, ?_⟩
  intro id call held
  obtain ⟨middle, stored, before⟩ := a.calls id call held
  obtain ⟨current, stored, after⟩ := b.calls id middle stored
  exact ⟨current, stored, Nat.le_trans before after⟩

theorem activate_calls (owner : Owner) (program : M α) (state : State α) : CallsGrow state (activate owner program state) := by
  refine ⟨?_, ?_⟩
  · cases program <;> simp [activate]
  · intro id call held
    exact ⟨call, (activate_old_call (Array.getElem?_eq_some_iff.mp held).choose).trans held, Nat.le_refl _⟩

private theorem set_calls (state : State α) (id : Nat) (call : Call α)
    (growth : ∀ previous, state.calls[id]? = some previous → previous.rank ≤ call.rank) :
    CallsGrow state {state with calls := state.calls.setIfInBounds id call} := by
  refine ⟨by simp, ?_⟩
  intro other previous held
  by_cases same : id = other
  · subst other
    exact ⟨call, by simp [(Array.getElem?_eq_some_iff.mp held).choose], growth previous held⟩
  · exact ⟨previous, by simpa [Array.getElem?_setIfInBounds, same] using held, Nat.le_refl _⟩

theorem Transition.calls_grow {programs : Array (M α)} {action before after}
    (executed : Transition programs action before after) : CallsGrow before after := by
  cases executed with
  | @commit β state id owner operation next value services issued lawful =>
    have grow := set_calls before id (.committed owner operation value next)
      (fun previous held => by rw [issued] at held; cases held; simp [Call.rank])
    exact ⟨grow.size, grow.calls⟩
  | @reply id _ _ executed =>
    simp only [step] at executed
    split at executed <;> try contradiction
    have retired := set_calls before id .retired (fun previous _ => previous.rank_le)
    split at executed
    · cases executed; exact retired
    · split at executed <;> try contradiction
      cases executed
      exact retired.trans (activate_calls _ _ _)
  | @crash worker _ _ executed =>
    simp only [step] at executed
    split at executed <;> try contradiction
    rename_i current held
    split at executed <;> try contradiction
    cases executed
    refine ⟨by simp, ?_⟩
    intro id call stored
    exact ⟨call.orphan ⟨worker, current.attempt⟩, by simp [Array.getElem?_map, stored], by simp [Call.rank_orphan]⟩
  | restart executed =>
    simp only [step] at executed
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    cases executed
    exact activate_calls _ _ _

namespace Repeated.Trace
variable {programs : Array (M α)} {again : α → Bool}

theorem calls_grow (trace : Repeated.Trace programs again) {first last : Nat} (later : first ≤ last) :
    CallsGrow (trace.states first) (trace.states last) := by
  have one time : CallsGrow (trace.states time) (trace.states (time + 1)) := by
    have executed := trace.execution time
    cases event : trace.events time with
    | none => simp only [event] at executed; rw [executed]; exact .refl _
    | some action =>
      simp only [event] at executed
      generalize future : trace.states (time + 1) = final at executed ⊢
      cases executed with
      | action performed => exact performed.calls_grow
      | iterate held found unfinished => exact activate_calls _ _ _
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
  induction offset with
  | zero => exact .refl _
  | succ offset ih => exact (ih (by omega)).trans (one (first + offset))

theorem commit_phases (trace : Repeated.Trace programs again) {time id : Nat}
    (event : trace.events time = some (.action (.commit id))) :
    (∃ call, (trace.states time).calls[id]? = some call ∧ call.rank = 0) ∧
      (∃ call, (trace.states (time + 1)).calls[id]? = some call ∧ call.rank = 1) := by
  have performed := trace.schedule.execution time (.commit id) (by simp [schedule, event])
  generalize future : trace.states (time + 1) = final at *
  dsimp only [schedule] at performed
  rw [future] at performed
  cases performed with
  | @commit β state id owner operation next value services issued lawful =>
    exact ⟨⟨_, issued, rfl⟩, ⟨.committed owner operation value next,
      by simp [(Array.getElem?_eq_some_iff.mp issued).choose], rfl⟩⟩

/-- A call identity can commit only once, even if its owner crashed. -/
theorem commit_once (trace : Repeated.Trace programs again) {first last id : Nat} (later : first < last)
    (committed : trace.events first = some (.action (.commit id))) :
    trace.events last ≠ some (.action (.commit id)) := by
  intro twice
  obtain ⟨call, held, phase⟩ := (trace.commit_phases committed).2
  obtain ⟨current, stored, monotone⟩ := (trace.calls_grow (by omega : first + 1 ≤ last)).calls id call held
  obtain ⟨pending, same, earlier⟩ := (trace.commit_phases twice).1
  rw [stored] at same
  cases same
  omega

/-- The finitely many requests already issued at a cut cannot keep producing
new commits forever. Requests that never commit need no timeout assumption. -/
theorem old_calls_stop (trace : Repeated.Trace programs again) (bound : Nat) :
    ∃ cut, ∀ time, cut ≤ time → ∀ id, id < bound → trace.events time ≠ some (.action (.commit id)) := by
  classical
  induction bound with
  | zero => exact ⟨0, by intro time later id impossible; omega⟩
  | succ bound ih =>
    obtain ⟨previous, old⟩ := ih
    by_cases occurs : ∃ time, trace.events time = some (.action (.commit bound))
    · obtain ⟨time, event⟩ := occurs
      refine ⟨max previous (time + 1), ?_⟩
      intro later beyond id inside
      by_cases smaller : id < bound
      · exact old later (by omega) id smaller
      · have same : id = bound := by omega
        subst id
        exact trace.commit_once (by omega) event
    · refine ⟨previous, ?_⟩
      intro time beyond id inside event
      by_cases smaller : id < bound
      · exact old time beyond id smaller event
      · have same : id = bound := by omega
        subst id
        exact occurs ⟨time, event⟩

end Repeated.Trace
end LeanCloud.Backend.Execution
