import LeanCloud.Proofs.BackendCallHistory

namespace LeanCloud.Backend.Execution
open LeanEff

def Call.abandoned : Call α → Bool
  | .pending _ _ none | .committed _ _ _ none => true
  | _ => false

def OrphansBefore (bound : Nat) (state : State α) : Prop :=
  ∀ (id : Nat) call, state.calls[id]? = some call → call.abandoned = true → id < bound

theorem OrphansBefore.activate {bound} {state : State α} (bounded : OrphansBefore bound state)
    (owner : Owner) (program : M α) : OrphansBefore bound (activate owner program state) := by
  intro id call held abandoned
  cases program with
  | pure value => exact bounded id call held abandoned
  | impure operation next =>
    change (state.calls.push _)[id]? = some call at held
    rw [Array.getElem?_push] at held
    split at held
    · cases held; cases abandoned
    · exact bounded id call held abandoned

private theorem OrphansBefore.retire {bound} {state : State α} (bounded : OrphansBefore bound state) (id : Nat) :
    OrphansBefore bound {state with calls := state.calls.setIfInBounds id .retired} := by
  intro other call held abandoned
  rw [Array.getElem?_setIfInBounds] at held
  split at held
  · split at held <;> cases held
    cases abandoned
  · exact bounded other call held abandoned

theorem Transition.orphans {programs : Array (M α)} {action before after bound}
    (executed : Transition programs action before after) (bounded : OrphansBefore bound before)
    (noCrash : ∀ worker, action ≠ .crash worker) : OrphansBefore bound after := by
  cases executed with
  | @commit β state id owner operation next value services issued lawful =>
    intro other call held abandoned
    rw [Array.getElem?_setIfInBounds] at held
    split at held
    · rename_i same
      subst other
      split at held
      · cases held
        exact bounded id _ issued (by cases next <;> exact abandoned)
      · cases held
    · exact bounded other call held abandoned
  | reply executed =>
    simp only [step] at executed
    split at executed <;> try contradiction
    split at executed
    · cases executed; exact bounded.retire _
    · split at executed <;> try contradiction
      cases executed
      exact (bounded.retire _).activate _ _
  | crash executed => exact False.elim (noCrash _ rfl)
  | restart executed =>
    simp only [step] at executed
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    cases executed
    exact bounded.activate _ _

namespace Repeated.Trace
variable {programs : Array (M α)} {again : α → Bool}

theorem orphans_bounded (trace : Repeated.Trace programs again) (cut : Nat)
    (noCrash : ∀ worker, trace.schedule.NoCrashesAfter worker cut) {time : Nat} (later : cut ≤ time) :
    OrphansBefore (trace.states cut).calls.size (trace.states time) := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
  induction offset with
  | zero => exact fun id call held _ => (Array.getElem?_eq_some_iff.mp held).choose
  | succ offset ih =>
    let time := cut + offset
    change OrphansBefore (trace.states cut).calls.size (trace.states (time + 1))
    have executed := trace.execution time
    cases event : trace.events time with
    | none => simp only [event] at executed; rw [executed]; exact ih (by omega)
    | some action =>
      simp only [event] at executed
      generalize future : trace.states (time + 1) = final at executed ⊢
      cases executed with
      | action performed =>
        apply performed.orphans (ih (by omega))
        intro worker same
        apply noCrash worker time (by dsimp [time]; omega)
        simp [schedule, event, same]
      | iterate held found unfinished => exact (ih (by omega)).activate _ _

/-- After the final crash, some finite suffix has no new orphan commits.
Old requests may commit arbitrarily late or never commit; neither choice can
consume infinitely many deliveries, because call identities are never reused. -/
def LiveCommits (trace : Repeated.Trace programs again) (cut : Nat) : Prop :=
  ∀ time, cut ≤ time →
    ∀ {β : Type} (id : Nat) (owner : Owner) (operation : Request β) (value : β) (next : Option (ArrsF Request β α)),
      trace.events time = some (.action (.commit id)) →
      (trace.states (time + 1)).calls[id]? = some (.committed owner operation value next) →
      ∃ rest, next = some rest

theorem eventually_live_commits (trace : Repeated.Trace programs again) (cut : Nat)
    (noCrash : ∀ worker, trace.schedule.NoCrashesAfter worker cut) :
    ∃ liveCut, cut ≤ liveCut ∧ LiveCommits trace liveCut := by
  obtain ⟨lastOld, stopped⟩ := trace.old_calls_stop (trace.states cut).calls.size
  refine ⟨max cut lastOld, by omega, ?_⟩
  intro time later β id owner operation value next event held
  cases next with
  | some rest => exact ⟨rest, rfl⟩
  | none =>
    have bounded := trace.orphans_bounded cut noCrash (time := time + 1) (by omega)
    have old := bounded id _ held rfl
    exact False.elim (stopped time (by omega) id old event)

end Repeated.Trace
end LeanCloud.Backend.Execution
