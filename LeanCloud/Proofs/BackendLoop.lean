import LeanCloud.Proofs.BackendQueue
import LeanCloud.Proofs.BackendPrefix

namespace LeanCloud.Backend.Proofs.Worker
open Lean LeanEff LeanCloud.Proofs

theorem step_bounded {program : Cloud Replay.M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : (node.exit == node.exit) = true)
    (state : Backend.State) (valid : Valid tree state)
    (active : route.Activated (Journal.view state)) (fuel : Nat) (worker : Replay.Worker) :
    Checked (Valid tree) ((ReplayInterpreter.Internal.step Replay.db Replay.noBlobs fuel program current).run)
      (fun actual handle final => (actual = .error exhausted ∧ fuel < sizeOf tree) ∨ ∃ response,
        actual = .ok response ∧ handle = worker ∧ Journal.Emits tree response final ∧
        Journal.StepProgress tree current node state response final) worker state := by
  by_cases enough : sizeOf tree ≤ fuel
  · apply Safe.weaken (step_safe whole supported route comparable sameExit state valid active fuel
      (Nat.le_trans route.fuel_bound enough) worker)
    intro returned final kept done
    obtain ⟨response, rfl, emitted, progress⟩ := done
    exact ⟨.ok response, worker, rfl, .inr ⟨response, rfl, rfl, emitted, progress⟩⟩
  · have enough' : route.prefixSteps + 1 ≤ fuel + sizeOf tree := Nat.le_trans route.fuel_bound (by omega)
    have safe := step_safe whole supported route comparable sameExit state valid active (fuel + sizeOf tree) enough' worker
    apply Safe.weaken (safe.prefix (step_truncates Replay.db Replay.noBlobs program supported current fuel (sizeOf tree) worker))
    intro returned final kept done
    rcases done with ⟨handle, rfl⟩ | ⟨response, rfl, emitted, progress⟩
    · exact ⟨.error exhausted, handle, rfl, .inl ⟨rfl, Nat.lt_of_not_ge enough⟩⟩
    · exact ⟨.ok response, worker, rfl, .inr ⟨response, rfl, rfl, emitted, progress⟩⟩

def expected [Codec α] (tree : ExecutionTree) : Except CloudError α :=
  (ReplayInterpreter.Internal.result (m := Id) tree.exit).run

/-- An ordinary returned outcome has a matching durable completion record.
Budget exhaustion may return before the workflow is complete. -/
def Answers [Codec α] (tree : ExecutionTree) (actual : Except CloudError α)
    (_ : Replay.Worker) (state : Backend.State) : Prop :=
  (actual = expected tree ∧ completed state = some (toJson tree.exit)) ∨ actual = .error exhausted

theorem result_eq [Codec α] (outcome : Exit) (worker : Replay.Worker) :
    (ReplayInterpreter.Internal.result (m := StateT Replay.Worker Replay.M) (α := α) outcome).run worker =
      pure ((ReplayInterpreter.Internal.result (m := Id) (α := α) outcome).run, worker) := by
  cases outcome with
  | success value =>
    simp only [ReplayInterpreter.Internal.result, ReplayInterpreter.Internal.decode]
    cases Codec.decode (α := α) value <;> rfl
  | failure error | cancelled reason => rfl

private theorem result_checked [Codec α] (tree : ExecutionTree) (worker : Replay.Worker)
    (state : Backend.State) (stored : completed state = some (toJson tree.exit)) :
    Checked (Valid tree) ((ReplayInterpreter.Internal.result (m := StateT Replay.Worker Replay.M) tree.exit).run)
      (Answers (α := α) tree) worker state := by
  unfold Checked
  rw [result_eq]
  exact .pure fun final bounded growth => ⟨expected tree, worker, rfl, .inl ⟨rfl, growth.completed _ stored⟩⟩

/-- Safety of the unchanged public worker loop under every allowed service
reply, interleaving and fuel budget. No completion or fairness premise is used. -/
theorem run_checked [Codec α] {program : Cloud Replay.M Json} {tree : ExecutionTree}
    (whole : Expansion program tree) (supported : PureProgram program)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (sameJson : (toJson tree.exit == toJson tree.exit) = true)
    (fuel : Nat) (worker : Replay.Worker) (state : Backend.State) (valid : Valid tree state) :
    Checked (Valid tree) ((ReplayInterpreter.Internal.run Replay.db Replay.noBlobs Replay.queue fuel program).run)
      (Answers (α := α) tree) worker state := by
  induction fuel generalizing worker state with
  | zero => exact .pure fun _ _ _ => ⟨.error exhausted, worker, rfl, .inr rfl⟩
  | succ fuel ih =>
    rw [ReplayInterpreter.Internal.run]
    apply Checked.bind ((next_checked tree worker state valid).except (ε := CloudError) valid
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
      apply Checked.bind (step_bounded whole supported route comparable (sameExit _ _ route.member)
        polled kept active (fuel + 1) handle) kept
      intro actual worker executed bounded later result
      rcases result with ⟨rfl, _⟩ | ⟨response, rfl, rfl, emitted, progress⟩
      · exact .pure fun _ _ _ => ⟨.error exhausted, worker, rfl, .inr rfl⟩
      · cases worker with
        | mk backend delivery =>
          cases backend
          dsimp only at held
          subst delivery
          have finished := (complete_checked sameJson location receipt response executed bounded emitted).except
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

end LeanCloud.Backend.Proofs.Worker
