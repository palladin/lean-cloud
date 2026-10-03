import LeanCloud.Proofs.BackendCallers
import LeanCloud.Proofs.BackendIteration

/-! Repetition is a proof view of the outer loop, before fixing its finite
fuel. Administrative iterates perform no service operation and only replace a
finished unfinished iteration. Every other event is the shared execution model. -/

namespace LeanCloud.Backend.Execution.Repeated
open LeanEff LeanCloud.Backend.Proofs

inductive Event where
  | action : Action → Event
  | iterate : Nat → Event
  deriving DecidableEq

inductive Transition (programs : Array (M α)) (again : α → Bool) : Event → State α → State α → Prop where
  | action {event before after} (executed : Execution.Transition programs event before after) :
      Transition programs again (.action event) before after
  | iterate {before : State α} {worker attempt value program}
      (held : before.workers[worker]? = some ⟨attempt, .finished value⟩)
      (found : programs[worker]? = some program) (unfinished : again value = true) :
      Transition programs again (.iterate worker) before (activate ⟨worker, attempt⟩ program before)

structure Trace (programs : Array (M α)) (again : α → Bool) where
  states : Nat → State α
  events : Nat → Option Event
  execution : ∀ time,
    match events time with
    | none => states (time + 1) = states time
    | some event => Transition programs again event (states time) (states (time + 1))

namespace Trace
variable {programs : Array (M α)} {again : α → Bool}

private theorem activate_workers_size (owner : Owner) (program : M α) (state : State α) :
    (activate owner program state).workers.size = state.workers.size := by
  cases program <;> simp [activate]

private theorem transition_workers_size {action before after}
    (executed : Execution.Transition programs action before after) : after.workers.size = before.workers.size := by
  cases executed with
  | commit issued lawful => rfl
  | reply executed =>
    simp only [Execution.step] at executed
    split at executed <;> try contradiction
    split at executed
    · cases executed; rfl
    · split at executed <;> try contradiction
      cases executed
      exact activate_workers_size _ _ _
  | crash executed =>
    simp only [Execution.step] at executed
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    cases executed
    simp
  | restart executed =>
    simp only [Execution.step] at executed
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    split at executed <;> try contradiction
    cases executed
    exact activate_workers_size _ _ _

theorem workers_size (trace : Trace programs again) (time : Nat) :
    (trace.states time).workers.size = (trace.states 0).workers.size := by
  induction time with
  | zero => rfl
  | succ time ih =>
    have executed := trace.execution time
    cases event : trace.events time with
    | none => simp only [event] at executed; rw [executed]; exact ih
    | some action =>
      simp only [event] at executed
      generalize future : trace.states (time + 1) = final at executed ⊢
      cases executed with
      | action performed => exact (transition_workers_size performed).trans ih
      | iterate held found unfinished => exact (activate_workers_size _ _ _).trans ih

theorem initial_workers_size (services : Backend.State) (programs : Array (M α)) :
    (Execution.initial services programs).workers.size = programs.size := by
  have fold (indices : List Nat) (state : State α) :
      (indices.foldl (fun state worker =>
        match programs[worker]? with
        | none => state
        | some program => activate ⟨worker, 0⟩ program state) state).workers.size = state.workers.size := by
    induction indices generalizing state with
    | nil => rfl
    | cons worker rest ih =>
      rw [List.foldl_cons, ih]
      cases programs[worker]? with
      | none => rfl
      | some program => exact activate_workers_size _ _ _
  exact (fold _ _).trans Array.size_map

def schedule (trace : Trace programs again) : Execution.Schedule programs where
  states := trace.states
  events time := match trace.events time with | some (.action action) => some action | _ => none
  execution time action same := by
    have executed := trace.execution time
    cases event : trace.events time with
    | none => simp [event] at same
    | some chosen =>
      cases chosen with
      | iterate worker => simp [event] at same
      | action actual =>
        simp only [event, Option.some.injEq] at same
        subst actual
        simp only [event] at executed
        cases executed with
        | action performed => exact performed
  administrative time absent := by
    have executed := trace.execution time
    cases event : trace.events time with
    | none =>
      simp only [event] at executed
      rw [executed]
      exact ⟨rfl, fun _ _ _ held _ => held, fun _ _ held => held⟩
    | some action =>
      cases action with
      | action actual => simp [event] at absent
      | iterate worker =>
        simp only [event] at executed
        generalize future : trace.states (time + 1) = final at executed ⊢
        cases executed with
        | @iterate _ _ attempt value program held found unfinished =>
          refine ⟨activate_preserves _ _ _, ?_, ?_⟩
          · intro other generation status stored active
            have different : worker ≠ other := by
              intro same
              subst other
              rw [held] at stored
              exact active value (congrArg Worker.status (Option.some.inj stored)).symm
            exact (activate_other different).trans stored
          · intro id call stored
            exact (activate_old_call (Array.getElem?_eq_some_iff.mp stored).choose).trans stored

structure WeaklyFair (trace : Trace programs again) : Prop where
  workers : trace.schedule.WeaklyFair
  iterate : ∀ time worker attempt value,
    (trace.states time).workers[worker]? = some ⟨attempt, .finished value⟩ → again value = true →
    ∃ later, time ≤ later ∧ trace.events later = some (.iterate worker)

/-- Queue fairness names a primitive commit and a publication identity. It
does not assume anything about the dequeuing continuation or step result. -/
def FairDelivery (trace : Trace programs again) : Prop :=
  PollingForever trace.states trace.schedule.events →
  ∀ cut id message,
    (trace.states cut).services.queue.messages[id]? = some message → message.acknowledged = false →
    ∃ n, cut ≤ n ∧
      ((∃ settled, (trace.states n).services.queue.messages[id]? = some settled ∧ settled.acknowledged = true) ∨
       ∃ call owner next location receipt,
         trace.events n = some (.action (.commit call)) ∧
         (trace.states (n + 1)).calls[call]? = some (.committed owner .dequeue (some (location, receipt)) next) ∧
         (trace.states (n + 1)).services.queue.receipts[receipt]? = some id)

theorem invariants (trace : Trace programs again)
    {valid : Backend.State → Prop} {grows : Backend.State → Backend.State → Prop}
    {post : Nat → α → Backend.State → Prop}
    (refl : ∀ state, grows state state)
    (trans : ∀ {a b c}, grows a b → grows b c → grows a c)
    (fresh : ∀ index program, programs[index]? = some program → ∀ state,
      valid state → ProgramSafe valid grows (post index) program state)
    (initial : AllSafe valid grows post (trace.states 0)) :
    (∀ time, AllSafe valid grows post (trace.states time)) ∧
      ∀ first last, first ≤ last → grows (trace.states first).services (trace.states last).services := by
  have one {time} (safe : AllSafe valid grows post (trace.states time)) :
      grows (trace.states time).services (trace.states (time + 1)).services ∧
      AllSafe valid grows post (trace.states (time + 1)) := by
    have executed := trace.execution time
    cases event : trace.events time with
    | none => simp only [event] at executed; rw [executed]; exact ⟨refl _, safe⟩
    | some action =>
      simp only [event] at executed
      generalize future : trace.states (time + 1) = final at executed ⊢
      cases executed with
      | action performed => exact LeanCloud.Backend.Proofs.Transition.safe refl trans fresh performed safe
      | iterate held found unfinished =>
        exact ⟨by rw [activate_preserves]; exact refl _, safe.activate _ _ (fresh _ _ found _ safe.services)⟩
  have kept time : AllSafe valid grows post (trace.states time) := by
    induction time with
    | zero => exact initial
    | succ time ih => exact (one ih).2
  refine ⟨kept, ?_⟩
  intro first last later
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
  induction offset with
  | zero => exact refl _
  | succ offset ih => exact trans (ih (by omega)) (one (kept (first + offset))).1

theorem linked (trace : Trace programs again) (initial : Linked (trace.states 0)) (time : Nat) :
    Linked (trace.states time) := by
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
      | action performed => exact performed.linked ih
      | iterate held found unfinished => exact ih.activate_inactive _ _ held (by intro id same; cases same)

end Trace
end LeanCloud.Backend.Execution.Repeated

namespace LeanCloud.Backend.Proofs.Iteration
open Lean LeanEff LeanCloud.Proofs

abbrev Trace (traversal : Nat) (source : Cloud Replay.M Json) (count : Nat) :=
  Execution.Repeated.Trace (Array.replicate count (program traversal source)) again

def Post (tree : ExecutionTree) (returned : Outcome) (final : Backend.State) : Prop :=
  ∃ actual worker, returned = .ok (actual, worker) ∧ Returned tree actual worker final

theorem certified {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (program traversal source))) :
    (∀ time, AllSafe (Accounting.Valid tree) Worker.Grows (fun _ => Post tree) (trace.states time)) ∧
      ∀ first last, first ≤ last → Worker.Grows (trace.states first).services (trace.states last).services := by
  have fresh (index : Nat) actual (found : (Array.replicate count (program traversal source))[index]? = some actual)
      state (valid : Accounting.Valid tree state) :
      ProgramSafe (Accounting.Valid tree) Worker.Grows (Post tree) actual state := by
    have same : actual = program traversal source := by
      exact (Array.mem_replicate.mp (Array.mem_of_getElem? found)).2
    subst actual
    exact checked whole supported comparable sameExit traversal enough state valid
  apply trace.invariants Worker.Grows.refl (fun a b => a.trans b) fresh
  rw [initialized]
  exact AllSafe.initial _ _ (Accounting.Valid.initial tree) fresh

theorem no_loss {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (program traversal source)))
    (time : Nat) :
    Worker.completed (trace.states time).services = some (toJson tree.exit) ∨ Accounting.Outstanding (trace.states time).services := by
  obtain ⟨kept, growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
  have root : (trace.states 0).services.queue.messages[0]? = some {location := Location.root} := by
    rw [initialized, Execution.initial_preserves]
    rfl
  obtain ⟨message, stored, same, _⟩ := (growth 0 time (Nat.zero_le _)).queue.messages 0 _ root
  exact Accounting.no_loss (kept time).services ⟨message, stored, same⟩

end LeanCloud.Backend.Proofs.Iteration
