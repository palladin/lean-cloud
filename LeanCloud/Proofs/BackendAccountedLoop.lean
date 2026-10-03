import LeanCloud.Proofs.BackendHandoff
import LeanCloud.Proofs.BackendEquivalence

namespace LeanCloud.Backend.Proofs.Accounting
open Lean LeanEff LeanCloud.Proofs
open Worker (exhausted Answers expected completed result_eq)

private theorem result_checked [Codec α] (tree : ExecutionTree) (worker : Replay.Worker)
    (state : Backend.State) (stored : completed state = some (toJson tree.exit)) :
    Checked tree ((ReplayInterpreter.Internal.result (m := StateT Replay.Worker Replay.M) tree.exit).run)
      (Answers (α := α) tree) worker state := by
  unfold Checked Worker.Checked
  rw [result_eq]
  exact .pure fun final bounded growth => ⟨expected tree, worker, rfl, .inl ⟨rfl, growth.completed _ stored⟩⟩

/-- Every acknowledgement issued by the public loop carries its handoff
certificate. It remains valid even if the worker crashes before the ack commits. -/
theorem run_checked [Codec α] {program : Cloud Replay.M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (sameJson : (toJson tree.exit == toJson tree.exit) = true)
    (fuel : Nat) (worker : Replay.Worker) (state : Backend.State) (valid : Valid tree state) :
    Checked tree ((ReplayInterpreter.Internal.run Replay.db Replay.noBlobs Replay.queue fuel program).run)
      (Answers (α := α) tree) worker state := by
  induction fuel generalizing worker state with
  | zero => exact .pure fun _ _ _ => ⟨.error exhausted, worker, rfl, .inr rfl⟩
  | succ fuel ih =>
    rw [ReplayInterpreter.Internal.run]
    apply Checked.bind (Worker.Checked.except (next_checked tree worker state valid) (ε := CloudError) valid
      (fun _ _ _ _ growth next => next.grow growth)) valid
    intro actual handle polled kept growth done
    obtain ⟨work, rfl, next⟩ := done
    cases work with
    | completed outcome =>
      have same := next.2.1
      subst outcome
      exact result_checked tree handle polled next.2.2
    | idle => exact ih handle polled kept
    | item location =>
      obtain ⟨receipt, held, ⟨node, route, active⟩, received⟩ := next
      have footprint := (Footprint.step (fuel + 1) program supported location handle).mono
        (second := NoAck) (by intro β operation allowed; cases operation <;> trivial)
      apply Checked.bind (account (Worker.step_bounded whole supported route comparable (sameExit _ _ route.member)
        polled kept.safety active (fuel + 1) handle) footprint) kept
      intro actual worker executed bounded later result
      rcases result with ⟨rfl, _⟩ | ⟨response, rfl, rfl, emitted, progress⟩
      · exact .pure fun _ _ _ => ⟨.error exhausted, worker, rfl, .inr rfl⟩
      · cases worker with
        | mk backend delivery =>
          cases backend
          dsimp only at held
          subst delivery
          have finished := Worker.Checked.except
            (complete_checked sameJson location receipt response route polled executed kept.safety later
              received progress bounded emitted)
              (ε := CloudError) bounded
              (fun _ _ _ _ growth result => ⟨result.1, result.2.grow growth⟩)
          apply Checked.bind finished bounded
          intro actual worker published publishedValid extended done
          obtain ⟨value, rfl, rfl, stored⟩ := done
          cases response with
          | done outcome =>
            change outcome = tree.exit at emitted
            subst outcome
            exact result_checked tree _ published stored
          | runnable _ => exact ih _ published publishedValid

theorem attempts_accounted [codec : Codec α] (program : ι → Cloud Replay.M α) (input : ι)
    {tree : ExecutionTree} (whole : Expansion (codec.encode <$> program input) tree)
    (supported : PureProgram (program input))
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (fuel : Array Nat) (trace : Execution.Trace (Worker.attempts program input fuel))
    (initialized : trace.states 0 = Execution.initial Replay.initial (Worker.attempts program input fuel))
    (time : Nat) :
    Worker.Grows (trace.states 0).services (trace.states time).services ∧
      AllSafe (Valid tree) Worker.Grows
        (fun _ returned final => ∃ actual handle, returned = .ok (actual, handle) ∧ Answers tree actual handle final)
        (trace.states time) := by
  let post := fun (_ : Nat) (returned : Except String (Except CloudError α × Replay.Worker)) final =>
    ∃ actual handle, returned = .ok (actual, handle) ∧ Answers tree actual handle final
  have fresh (index : Nat) attempt (found : (Worker.attempts program input fuel)[index]? = some attempt)
      state (valid : Valid tree state) : ProgramSafe (Valid tree) Worker.Grows (post index) attempt state := by
    simp only [Worker.attempts, Array.getElem?_map] at found
    cases budget : fuel[index]? with
    | none => simp [budget] at found
    | some amount =>
      simp only [budget, Option.map_some] at found
      cases found
      exact run_checked whole (supported.map codec.encode) comparable sameExit
        (comparable_completion tree comparable) amount ⟨(), none⟩ state valid
  have initial : AllSafe (Valid tree) Worker.Grows post (trace.states 0) := by
    rw [initialized]
    exact AllSafe.initial _ _ (Valid.initial tree) fresh
  exact trace_safe Worker.Grows.refl (fun a b => a.trans b) fresh trace initial time

/-- At every point of the actual concurrent execution, completion is durable
or useful unacknowledged work remains. Crashes, lost replies and duplicate
deliveries may occur arbitrarily; this theorem has no fairness premise. -/
theorem attempts_no_loss [codec : Codec α] (program : ι → Cloud Replay.M α) (input : ι)
    {tree : ExecutionTree} (whole : Expansion (codec.encode <$> program input) tree)
    (supported : PureProgram (program input))
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (fuel : Array Nat) (trace : Execution.Trace (Worker.attempts program input fuel))
    (initialized : trace.states 0 = Execution.initial Replay.initial (Worker.attempts program input fuel))
    (time : Nat) :
    completed (trace.states time).services = some (toJson tree.exit) ∨ Outstanding (trace.states time).services := by
  obtain ⟨growth, safe⟩ := attempts_accounted program input whole supported comparable sameExit fuel trace initialized time
  have start : (trace.states 0).services = Replay.initial := by
    rw [initialized]
    exact Execution.initial_preserves _ _
  have root : (trace.states 0).services.queue.messages[0]? = some { location := Location.root } := by
    rw [start]
    rfl
  obtain ⟨message, stored, same, _⟩ := growth.queue.messages 0 _ root
  exact no_loss safe.services ⟨message, stored, same⟩

end LeanCloud.Backend.Proofs.Accounting
