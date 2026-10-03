import LeanCloud.Proofs.BackendRepeated

namespace LeanCloud.Backend.Execution
open LeanEff

/-- Conversely, every waiting worker has its own live service call. Together
with `Linked`, this rules out stuck dangling waiters and misdirected replies. -/
def Located (state : State α) : Prop :=
  ∀ (worker attempt id : Nat), state.workers[worker]? = some ⟨attempt, .waiting id⟩ →
    ∃ call, state.calls[id]? = some call ∧ call.caller = some ⟨worker, attempt⟩

theorem activate_located (owner : Owner) (program : M α) (state : State α)
    (others : ∀ worker attempt id, worker ≠ owner.worker →
      state.workers[worker]? = some ⟨attempt, .waiting id⟩ →
      ∃ call, state.calls[id]? = some call ∧ call.caller = some ⟨worker, attempt⟩) :
    Located (activate owner program state) := by
  intro worker attempt id held
  by_cases same : owner.worker = worker
  · cases program with
    | pure value => simp [activate, same, Array.getElem?_setIfInBounds_self] at held
    | impure operation next =>
      simp only [activate, same, Array.getElem?_setIfInBounds_self] at held
      split at held
      · have equal := Option.some.inj held
        have attempts := congrArg Worker.attempt equal
        dsimp only at attempts
        have ids := Status.waiting.inj (congrArg Worker.status equal)
        subst attempt
        subst id
        exact ⟨.pending owner operation (some next), by simp [activate], by cases owner; simp_all [Call.caller]⟩
      · cases held
  · have previous := (activate_other same).symm.trans held
    obtain ⟨call, stored, caller⟩ := others worker attempt id (Ne.symm same) previous
    exact ⟨call, (activate_old_call (Array.getElem?_eq_some_iff.mp stored).choose).trans stored, caller⟩

theorem Located.activate {state : State α} (located : Located state) (owner : Owner) (program : M α) :
    Located (Execution.activate owner program state) :=
  activate_located owner program state (fun worker attempt id _ => located worker attempt id)

theorem Transition.located {programs : Array (M α)} {action before after}
    (executed : Transition programs action before after) (located : Located before) : Located after := by
  cases executed with
  | @commit β state other owner operation next value services issued lawful =>
    intro worker attempt id held
    obtain ⟨call, stored, caller⟩ := located worker attempt id held
    by_cases same : other = id
    · subst other
      rw [issued] at stored
      cases stored
      exact ⟨.committed owner operation value next,
        by simp [(Array.getElem?_eq_some_iff.mp issued).choose], by cases next <;> exact caller⟩
    · exact ⟨call, by simpa [Array.getElem?_setIfInBounds, same] using stored, caller⟩
  | @reply other _ _ executed =>
    simp only [step] at executed
    split at executed <;> try contradiction
    rename_i β owner operation value next held
    split at executed
    · cases executed
      intro worker attempt id waiting
      obtain ⟨call, stored, caller⟩ := located worker attempt id waiting
      have different : other ≠ id := by
        intro same
        subst other
        rw [held] at stored
        cases stored
        cases caller
      exact ⟨call, by simpa [Array.getElem?_setIfInBounds, different] using stored, caller⟩
    · rename_i rest
      split at executed <;> try contradiction
      cases executed
      apply activate_located
      intro worker attempt id different waiting
      obtain ⟨call, stored, caller⟩ := located worker attempt id waiting
      have apart : other ≠ id := by
        intro same
        subst other
        rw [held] at stored
        cases stored
        have equal := congrArg Owner.worker (Option.some.inj caller)
        exact different equal.symm
      exact ⟨call, by simpa [Array.getElem?_setIfInBounds, apart] using stored, caller⟩
  | @crash other _ _ executed =>
    simp only [step] at executed
    split at executed <;> try contradiction
    rename_i current currentStored
    split at executed <;> try contradiction
    cases executed
    intro worker attempt id waiting
    have different : other ≠ worker := by
      intro same
      subst other
      simp [Array.getElem?_setIfInBounds_self] at waiting
    have previous : before.workers[worker]? = some ⟨attempt, .waiting id⟩ := by
      simpa [Array.getElem?_setIfInBounds, different] using waiting
    obtain ⟨call, stored, caller⟩ := located worker attempt id previous
    refine ⟨call.orphan ⟨other, current.attempt⟩, by simp [Array.getElem?_map, stored], ?_⟩
    rw [Call.caller_orphan, caller]
    simp [BEq.beq, instBEqOwner.beq, Ne.symm different]
  | restart executed =>
    simp only [step] at executed
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    cases executed
    exact located.activate _ _

theorem initial_located (services : Backend.State) (programs : Array (M α)) : Located (initial services programs) := by
  have fold (indices : List Nat) (state : State α) (located : Located state) :
      Located (indices.foldl (fun state worker =>
        match programs[worker]? with
        | none => state
        | some program => activate ⟨worker, 0⟩ program state) state) := by
    induction indices generalizing state with
    | nil => exact located
    | cons worker rest ih =>
      rw [List.foldl_cons]
      cases programs[worker]? with
      | none => exact ih state located
      | some program => exact ih _ (located.activate _ _)
  apply fold
  intro worker attempt id held
  simp only [Array.getElem?_map] at held
  cases programs[worker]? <;> simp at held

theorem Repeated.Trace.located {programs : Array (M α)} {again : α → Bool}
    (trace : Repeated.Trace programs again) (initial : Located (trace.states 0)) (time : Nat) :
    Located (trace.states time) := by
  induction time with
  | zero => exact initial
  | succ time ih =>
    have executed := trace.execution time
    cases event : trace.events time with
    | none => simp only [event] at executed; rw [executed]; exact ih
    | some action =>
      simp only [event] at executed
      generalize future : trace.states (time + 1) = final at executed ⊢
      cases executed with
      | action performed => exact performed.located ih
      | iterate held found unfinished => exact ih.activate _ _

end LeanCloud.Backend.Execution
