import LeanCloud.Proofs.BackendRepeated

namespace LeanCloud.Backend.Proofs
open LeanEff Execution

/-- A syntactic assertion about every issued request and its continuation.
This will identify dequeue's caller without placing it in queue fairness. -/
def Program.protocol (signature : {β : Type} → Request β → (β → Program α) → Prop) : Program α → Prop
  | .pure _ => True
  | .request operation next => signature operation next ∧ ∀ value, (next value).protocol signature

def CallProtocol (signature : {β : Type} → Request β → (β → Program α) → Prop) : Call α → Prop
  | .pending _ operation (some next) | .committed _ operation _ (some next) =>
      (Program.request operation (Program.ofArrs next)).protocol signature
  | _ => True

def AllProtocol (signature : {β : Type} → Request β → (β → Program α) → Prop) (state : Execution.State α) : Prop :=
  ∀ (id : Nat) call, state.calls[id]? = some call → CallProtocol signature call

theorem CallProtocol.orphan {signature : {β : Type} → Request β → (β → Program α) → Prop}
    {call : Call α} (valid : CallProtocol signature call) (owner : Owner) :
    CallProtocol signature (call.orphan owner) := by
  cases call with
  | pending caller operation next | committed caller operation value next =>
    cases next <;> by_cases same : (caller == owner) = true <;>
      simp_all [CallProtocol, Call.orphan]
  | retired => trivial

theorem AllProtocol.set {signature : {β : Type} → Request β → (β → Program α) → Prop}
    {state : Execution.State α} (valid : AllProtocol signature state) (id : Nat) (call : Call α)
    (permitted : CallProtocol signature call) :
    AllProtocol signature {state with calls := state.calls.setIfInBounds id call} := by
  intro other actual held
  rw [Array.getElem?_setIfInBounds] at held
  split at held
  · split at held
    · cases held; exact permitted
    · cases held
  · exact valid other actual held

theorem AllProtocol.activate {signature : {β : Type} → Request β → (β → Program α) → Prop}
    {state : Execution.State α} (valid : AllProtocol signature state) (owner : Owner) (program : M α)
    (permitted : (Program.ofEff program).protocol signature) : AllProtocol signature (activate owner program state) := by
  cases program with
  | pure value => exact valid
  | impure operation next =>
    intro id call held
    change (state.calls.push _)[id]? = some call at held
    rw [Array.getElem?_push] at held
    split at held
    · cases held; exact permitted
    · exact valid id call held

theorem Transition.protocol {signature : {β : Type} → Request β → (β → Program α) → Prop}
    {programs : Array (M α)} {action before after}
    (fresh : ∀ (id : Nat) program, programs[id]? = some program → (Program.ofEff program).protocol signature)
    (executed : Execution.Transition programs action before after) (valid : AllProtocol signature before) :
    AllProtocol signature after := by
  cases executed with
  | @commit β state id owner operation next value services issued lawful =>
    apply AllProtocol.set valid
    have permitted := valid _ _ issued
    cases next <;> exact permitted
  | reply executed =>
    simp only [Execution.step] at executed
    split at executed <;> try contradiction
    rename_i β owner operation value next stored
    have permitted := valid _ _ stored
    split at executed
    · cases executed; exact valid.set _ .retired trivial
    · rename_i rest
      split at executed <;> try contradiction
      cases executed
      apply (valid.set _ .retired trivial).activate
      rw [Program.ofEff_apply]
      exact permitted.2 value
  | crash executed =>
    simp only [Execution.step] at executed
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    cases executed
    intro id call held
    rw [Array.getElem?_map] at held
    cases stored : before.calls[id]? with
    | none => simp [stored] at held
    | some original =>
      simp only [stored, Option.map_some] at held
      cases held
      exact (valid id original stored).orphan _
  | restart executed =>
    simp only [Execution.step] at executed
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    rename_i program found
    split at executed <;> try contradiction
    cases executed
    exact valid.activate _ _ (fresh _ _ found)

theorem initial_protocol {signature : {β : Type} → Request β → (β → Program α) → Prop}
    (services : Backend.State) (programs : Array (M α))
    (fresh : ∀ (id : Nat) program, programs[id]? = some program → (Program.ofEff program).protocol signature) :
    AllProtocol signature (initial services programs) := by
  have fold (indices : List Nat) (state : Execution.State α) (valid : AllProtocol signature state) :
      AllProtocol signature (indices.foldl (fun state worker =>
        match programs[worker]? with
        | none => state
        | some program => activate ⟨worker, 0⟩ program state) state) := by
    induction indices generalizing state with
    | nil => exact valid
    | cons worker rest ih =>
      rw [List.foldl_cons]
      cases found : programs[worker]? with
      | none => exact ih state valid
      | some program => exact ih _ (valid.activate _ _ (fresh worker program found))
  exact fold _ _ (by intro id call absent; simp at absent)

theorem repeated_protocol {signature : {β : Type} → Request β → (β → Program α) → Prop}
    {programs : Array (M α)} {again : α → Bool} (trace : Execution.Repeated.Trace programs again)
    (fresh : ∀ (id : Nat) program, programs[id]? = some program → (Program.ofEff program).protocol signature)
    (initial : AllProtocol signature (trace.states 0)) (time : Nat) : AllProtocol signature (trace.states time) := by
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
      | action performed => exact Transition.protocol fresh performed ih
      | iterate held found unfinished => exact ih.activate _ _ (fresh _ _ found)

end LeanCloud.Backend.Proofs
