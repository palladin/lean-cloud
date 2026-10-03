import LeanCloud.Proofs.BackendPolling
import LeanCloud.Proofs.BackendOrphans
import LeanCloud.Proofs.BackendStable

namespace LeanCloud.Backend.Proofs.Iteration
open Lean LeanEff LeanCloud.Proofs Execution

private def BornAfter (origin current : Backend.State) : Prop :=
  ∀ (id : Nat) message, current.queue.messages[id]? = some message → origin.queue.messages.size ≤ id →
    Journal.Grows origin message.published.state

private theorem born_commit {origin before after : Backend.State} {operation : Request β} {value : β}
    (born : BornAfter origin before) (growth : Worker.Grows origin before)
    (law : Commits before operation value after) : BornAfter origin after := by
  intro id message held fresh
  cases operation with
  | get key => obtain ⟨_, rfl⟩ := law; exact born id message held fresh
  | put key actual =>
    cases value with
    | false => obtain ⟨_, rfl⟩ := law; exact born id message held fresh
    | true => rw [law.2.2.1] at held; exact born id message held fresh
  | enqueue location =>
    obtain ⟨rfl, rfl⟩ := law
    rw [Array.getElem?_push] at held
    split at held
    · cases held; exact growth.journal.to_snapshot
    · exact born id message held fresh
  | dequeue =>
    cases value with
    | none => have same : after = before := law; subst after; exact born id message held fresh
    | some pair => obtain ⟨_, _, _, _, _, rfl⟩ := law; exact born id message held fresh
  | acknowledge receipt =>
    cases value with
    | false => have same : after = before := law; subst after; exact born id message held fresh
    | true =>
      obtain ⟨selected, previous, delivered, stored, rfl⟩ := law
      rw [Array.getElem?_setIfInBounds] at held
      split at held
      · rename_i same
        subst id
        split at held
        · cases held; exact born selected previous stored fresh
        · cases held
      · exact born id message held fresh

theorem publications_after {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (program traversal source)))
    {cut time : Nat} (later : cut ≤ time) (id : Nat) (message : Backend.Message)
    (held : (trace.states time).services.queue.messages[id]? = some message)
    (fresh : (trace.states cut).services.queue.messages.size ≤ id) :
    Journal.Grows (trace.states cut).services message.published.state := by
  obtain ⟨kept, growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
  have born {time : Nat} (later : cut ≤ time) : BornAfter (trace.states cut).services (trace.states time).services := by
    obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le later
    induction offset with
    | zero =>
      simp only [Nat.add_zero]
      intro id message held fresh
      have inside := (Array.getElem?_eq_some_iff.mp held).choose
      omega
    | succ offset ih =>
      let time := cut + offset
      change BornAfter (trace.states cut).services (trace.states (time + 1)).services
      have executed := trace.execution time
      cases event : trace.events time with
      | none => simp only [event] at executed; rw [executed]; exact ih (by omega)
      | some action =>
        simp only [event] at executed
        generalize future : trace.states (time + 1) = final at executed ⊢
        cases executed with
        | action performed =>
          rcases performed.service_sound with same | ⟨β, operation, value, law⟩
          · rw [same]; exact ih (by omega)
          · exact born_commit (ih (by omega)) (growth cut time (by dsimp [time]; omega)) law
        | iterate held found unfinished =>
          rw [activate_preserves]
          exact ih (by omega)
  exact born later id message held fresh

/-- After orphan commits stop, queue fairness yields a settled publication or
a live delivery whose actual continuation publishes the replay response. -/
theorem fair_delivery {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (program traversal source)))
    (fair : trace.schedule.WeaklyFair) (deliveries : trace.FairDelivery)
    (demand : PollingForever trace.states trace.schedule.events) (cut : Nat)
    (noCrash : ∀ worker, trace.schedule.NoCrashesAfter worker cut) (live : trace.LiveCommits cut)
    (id : Nat) (message : Backend.Message)
    (stored : (trace.states cut).services.queue.messages[id]? = some message) :
    (∃ time current, cut ≤ time ∧ (trace.states time).services.queue.messages[id]? = some current ∧ current.acknowledged = true) ∨
    ∃ start node, ∃ _route : TreeRoute tree Location.root message.location node,
      ∃ time response, cut < start ∧ start ≤ time ∧
        Published tree message.location node (trace.states start).services response (trace.states time).services := by
  cases acknowledged : message.acknowledged with
  | true => exact .inl ⟨cut, message, Nat.le_refl _, stored, acknowledged⟩
  | false =>
    obtain ⟨time, beyond, settled | selected⟩ := deliveries demand cut id message stored acknowledged
    · obtain ⟨current, held, acked⟩ := settled
      exact .inl ⟨time, current, beyond, held, acked⟩
    · obtain ⟨call, owner, next, location, receipt, event, saved, received⟩ := selected
      obtain ⟨rest, rfl⟩ := live time beyond call owner .dequeue (some (location, receipt)) next event saved
      obtain ⟨kept, growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
      have performed := trace.schedule.execution time (.commit call) (by simp [Execution.Repeated.Trace.schedule, event])
      obtain ⟨issued, law⟩ := performed.commit_reply saved
      obtain ⟨_active, selectedId, actual, actualReceipt, actualStored, payload⟩ :=
        (Worker.dequeue_preserves (kept time).services.safety law).2.2 location receipt rfl
      have equalId := Option.some.inj (received.symm.trans actualReceipt)
      subst selectedId
      obtain ⟨current, currentStored, same, _⟩ := (growth cut (time + 1) (by omega)).queue.messages id message stored
      have equalMessage := Option.some.inj (actualStored.symm.trans currentStored)
      subst current
      have locationSame : location = message.location := payload.symm.trans same
      obtain ⟨node, route, later, response, returned, afterReturn, finished, published, correct⟩ :=
        dequeue_publishes whole supported comparable sameExit traversal enough trace initialized fair time call owner location receipt rest event saved
          (fun n after => noCrash owner.worker n (by omega))
      rw [locationSame] at route published
      exact .inr ⟨time + 1, node, route, later, response, by omega, by omega, published⟩

end LeanCloud.Backend.Proofs.Iteration
