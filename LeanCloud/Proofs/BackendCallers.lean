import LeanCloud.Proofs.BackendLiveness

namespace LeanCloud.Backend.Execution
open LeanEff

def Call.caller : Call α → Option Owner
  | .pending owner _ (some _) | .committed owner _ _ (some _) => some owner
  | _ => none

/-- Every live reply belongs to exactly the worker waiting for its call id.
Orphaned calls retain their service request but have no volatile caller. -/
def Linked (state : State α) : Prop :=
  ∀ (id : Nat) call, state.calls[id]? = some call → ∀ owner,
    call.caller = some owner → state.workers[owner.worker]? = some ⟨owner.attempt, .waiting id⟩

theorem Call.caller_orphan (call : Call α) (owner : Owner) :
    (call.orphan owner).caller = (call.caller.bind fun caller => if caller == owner then none else some caller) := by
  cases call with
  | pending caller operation next | committed caller operation value next =>
    cases next <;> by_cases same : (caller == owner) = true <;> simp [Call.orphan, Call.caller, same]
  | retired => rfl

theorem owner_beq (a b : Owner) : (a == b) = true ↔ a = b := by
  cases a; cases b
  simp [BEq.beq, instBEqOwner.beq]

theorem Linked.activate {state : State α} (linked : Linked state) (owner : Owner) (program : M α)
    (inside : owner.worker < state.workers.size)
    (free : ∀ (id : Nat) call, state.calls[id]? = some call → ∀ caller,
      call.caller = some caller → caller.worker ≠ owner.worker) : Linked (activate owner program state) := by
  intro id call held caller live
  cases program with
  | pure value =>
    have old := linked id call held caller live
    simpa [Execution.activate, Ne.symm (free id call held caller live)] using old
  | impure operation next =>
    change (state.calls.push _)[id]? = some call at held
    rw [Array.getElem?_push] at held
    split at held
    · rename_i same
      subst id
      cases held
      cases live
      simp [Execution.activate, inside]
    · have old := linked id call held caller live
      simpa [Execution.activate, Ne.symm (free id call held caller live)] using old

theorem Linked.retire {state : State α} (linked : Linked state) (id : Nat) :
    Linked {state with calls := state.calls.setIfInBounds id .retired} := by
  intro other call held owner live
  rw [Array.getElem?_setIfInBounds] at held
  split at held
  · split at held <;> cases held
    cases live
  · exact linked other call held owner live

theorem Linked.commit {state : State α} (linked : Linked state) {id : Nat} {owner : Owner}
    {operation : Request β} {next : Option (ArrsF Request β α)}
    (held : state.calls[id]? = some (.pending owner operation next)) (value : β) (services : Backend.State) :
    Linked {state with services, calls := state.calls.setIfInBounds id (.committed owner operation value next)} := by
  intro other call stored caller live
  rw [Array.getElem?_setIfInBounds] at stored
  split at stored
  · rename_i same
    subst other
    split at stored
    · cases stored
      exact linked id _ held caller (by cases next <;> exact live)
    · cases stored
  · exact linked other call stored caller live

theorem Linked.crash {programs : Array (M α)} {before after : State α} (linked : Linked before) {worker}
    (executed : step programs (.crash worker) before = .ok after) : Linked after := by
  simp only [step] at executed
  split at executed <;> try contradiction
  rename_i current stored
  split at executed <;> try contradiction
  cases executed
  intro id call held owner live
  rw [Array.getElem?_map] at held
  cases found : before.calls[id]? with
  | none => simp [found] at held
  | some original =>
    simp only [found, Option.map_some] at held
    cases held
    rw [Call.caller_orphan] at live
    cases caller : original.caller with
    | none => simp [caller] at live
    | some prior =>
      simp only [caller, Option.bind_some] at live
      split at live
      · cases live
      · rename_i different
        cases live
        have waiting := linked id original found owner caller
        have apart : worker ≠ owner.worker := by
          intro same
          rw [same, waiting] at stored
          have attempts := congrArg Worker.attempt (Option.some.inj stored)
          have equal : owner = ⟨worker, current.attempt⟩ := by cases owner; simp_all
          exact different ((owner_beq _ _).mpr equal)
        simpa [Array.getElem?_setIfInBounds, apart] using waiting

theorem Linked.restart {programs : Array (M α)} {before after : State α} (linked : Linked before) {worker}
    (executed : step programs (.restart worker) before = .ok after) : Linked after := by
  simp only [step] at executed
  split at executed <;> try contradiction
  rename_i current stored
  split at executed <;> try contradiction
  split at executed <;> try contradiction
  rename_i stopped
  cases executed
  apply linked.activate _ _ (Array.getElem?_eq_some_iff.mp stored).choose
  intro id call held owner live same
  have waiting := linked id call held owner live
  rw [same, stored] at waiting
  have status := congrArg Worker.status (Option.some.inj waiting)
  rw [stopped] at status
  cases status

theorem Linked.reply {programs : Array (M α)} {before after : State α} (linked : Linked before) {id}
    (executed : step programs (.reply id) before = .ok after) : Linked after := by
  simp only [step] at executed
  split at executed <;> try contradiction
  rename_i β owner operation value next held
  split at executed
  · cases executed; exact linked.retire id
  · rename_i rest
    split at executed <;> try contradiction
    rename_i owns
    have waiting := (owns_iff owner id before).mp owns
    cases executed
    apply (linked.retire id).activate _ _ (Array.getElem?_eq_some_iff.mp waiting).choose
    intro other call stored caller live same
    rw [Array.getElem?_setIfInBounds] at stored
    split at stored
    · split at stored <;> cases stored
      cases live
    · rename_i different
      have otherWaiting := linked other call stored caller live
      rw [same, waiting] at otherWaiting
      have equal := Status.waiting.inj (congrArg Worker.status (Option.some.inj otherWaiting))
      exact different equal

theorem Linked.activate_inactive {state : State α} (linked : Linked state) (owner : Owner) (program : M α)
    {previous : Worker α} (held : state.workers[owner.worker]? = some previous)
    (inactive : ∀ id, previous.status ≠ .waiting id) : Linked (Execution.activate owner program state) := by
  apply linked.activate owner program (Array.getElem?_eq_some_iff.mp held).choose
  intro id call stored caller live same
  have waiting := linked id call stored caller live
  rw [same, held] at waiting
  exact inactive id (congrArg Worker.status (Option.some.inj waiting))

theorem initial_linked (services : Backend.State) (programs : Array (M α)) :
    Linked (initial services programs) := by
  have fold (indices : List Nat) (state : State α) (linked : Linked state)
      (distinct : indices.Nodup)
      (stopped : ∀ index ∈ indices, ∃ attempt, state.workers[index]? = some ⟨attempt, .stopped⟩) :
      Linked (indices.foldl (fun state worker =>
        match programs[worker]? with
        | none => state
        | some program => activate ⟨worker, 0⟩ program state) state) := by
    induction indices generalizing state with
    | nil => exact linked
    | cons worker rest ih =>
      rw [List.foldl_cons]
      cases found : programs[worker]? with
      | none => exact ih state linked distinct.tail (fun index member => stopped index (by simp [member]))
      | some program =>
        obtain ⟨attempt, held⟩ := stopped worker (by simp)
        apply ih _ (linked.activate_inactive ⟨worker, 0⟩ program held (by intro id same; cases same)) distinct.tail
        intro index member
        obtain ⟨attempt, previous⟩ := stopped index (by simp [member])
        refine ⟨attempt, ?_⟩
        have different : worker ≠ index := by
          intro same
          subst index
          exact (List.nodup_cons.mp distinct).1 member
        exact (activate_other different).trans previous
  apply fold _ _ (by intro id call absent; simp at absent) List.nodup_range
  intro index member
  have inside := List.mem_range.mp member
  refine ⟨0, ?_⟩
  simp [Array.getElem?_map, Array.getElem?_eq_getElem inside]

theorem Transition.linked {programs : Array (M α)} {action before after}
    (transition : Transition programs action before after) (linked : Linked before) : Linked after := by
  cases transition with
  | commit issued lawful => exact linked.commit issued _ _
  | reply executed => exact linked.reply executed
  | crash executed => exact linked.crash executed
  | restart executed => exact linked.restart executed

end LeanCloud.Backend.Execution
