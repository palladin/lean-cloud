import LeanCloud.Proofs.BackendDelivery
import LeanCloud.Proofs.BackendWorkerLiveness

namespace LeanCloud.Backend.Proofs.Iteration
open Lean LeanEff LeanCloud.Proofs Execution

private theorem started_dequeues (traversal : Nat) (source : Cloud Replay.M Json)
    (trace : Trace traversal source count) (fair : trace.schedule.WeaklyFair)
    (unfinished : ∀ n, Worker.completed (trace.states n).services = none)
    (time : Nat) (owner : Owner)
    (started : Continues owner (Program.ofEff (program traversal source)) (trace.states time))
    (noCrash : trace.schedule.NoCrashesAfter owner.worker time) :
    ∃ later call reply next, time ≤ later ∧ trace.schedule.events later = some (.commit call) ∧
      (trace.states (later + 1)).calls[call]? = some (.committed owner .dequeue reply (some next)) := by
  rw [normalized] at started
  obtain ⟨call, next, waiting, code⟩ := started.request_view
  obtain ⟨readAt, afterRead, reading, event⟩ := trace.schedule.eventually_commit fair waiting noCrash
  obtain ⟨value, saved, law⟩ := reading.committed (trace.schedule.execution readAt _ event)
  have empty : value = none := law.1.trans (unfinished readAt)
  subst value
  obtain ⟨replyAt, afterReply, responding, reply⟩ := trace.schedule.eventually_reply fair saved
    (fun n beyond => noCrash n (by omega))
  have activated := responding.replied (trace.schedule.execution replyAt _ reply)
  dsimp only [Execution.Repeated.Trace.schedule] at activated
  have continuing : Continues owner
      (.request .dequeue (fun reply => Program.ofEff (dispatch traversal source reply)))
      (trace.states (replyAt + 1)) := by
    have resumed : Continues owner (Program.ofArrs next none) (trace.states (replyAt + 1)) := by
      rw [activated, ← Program.ofEff_apply]
      exact activate_continues _ owner _ (Array.getElem?_eq_some_iff.mp responding.1).choose
    simpa only [code] using resumed
  obtain ⟨dequeueCall, afterDequeue, waiting, _code⟩ := continuing.request_view
  obtain ⟨dequeuedAt, afterDequeue, waiting, event⟩ := trace.schedule.eventually_commit fair waiting
    (fun n beyond => noCrash n (by omega))
  obtain ⟨reply, committed, _law⟩ := waiting.committed (trace.schedule.execution dequeuedAt _ event)
  exact ⟨dequeuedAt, dequeueCall, reply, _, by omega, event, committed.2⟩

theorem iteration_returns {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (program traversal source)))
    (fair : trace.schedule.WeaklyFair) (worker : Fin count) (cut : Nat)
    (noCrash : trace.schedule.NoCrashesAfter worker cut) :
    ∃ later attempt outcome, cut ≤ later ∧
      (trace.states later).workers[worker.val]? = some ⟨attempt, .finished (.ok (.ok outcome, ⟨(), none⟩))⟩ ∧
      ∀ value, outcome = some value → value = tree.exit ∧ Worker.completed (trace.states later).services = some (toJson value) := by
  obtain ⟨kept, growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
  have fresh (id : Nat) actual (found : (Array.replicate count (program traversal source))[id]? = some actual)
      state (valid : Accounting.Valid tree state) : ProgramSafe (Accounting.Valid tree) Worker.Grows (Post tree) actual state := by
    have same := (Array.mem_replicate.mp (Array.mem_of_getElem? found)).2
    subst actual
    exact checked whole supported comparable sameExit traversal enough state valid
  have size : (trace.states cut).workers.size = count := by
    rw [trace.workers_size, initialized, Execution.Repeated.Trace.initial_workers_size, Array.size_replicate]
  have inside : worker.val < (trace.states cut).workers.size := by omega
  have located time := trace.located (by rw [initialized]; exact initial_located _ _) time
  obtain ⟨later, attempt, returned, afterReturn, finished, actual, handle, equal, outcome, same, clean, result⟩ :=
    worker_returns (grows := Worker.Grows) trace.schedule fair Worker.Grows.refl (fun a b => a.trans b)
      kept growth fresh located worker cut (program traversal source) (by simp [worker.isLt])
      (trace.states cut).workers[worker.val] (Array.getElem?_eq_getElem inside) noCrash
  subst actual
  subst handle
  subst returned
  exact ⟨later, attempt, outcome, afterReturn, finished, result⟩

/-- Unfinished workers keep issuing dequeues. Thus the queue's conditional
fair-delivery law has real consumer demand; completion does not owe more polls. -/
theorem polling_forever {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (program traversal source)))
    (fair : trace.WeaklyFair) (nonempty : 0 < count) (cut : Nat)
    (noCrash : ∀ worker, trace.schedule.NoCrashesAfter worker cut)
    (unfinished : ∀ n, Worker.completed (trace.states n).services ≠ some (toJson tree.exit)) :
    PollingForever trace.states trace.schedule.events := by
  obtain ⟨kept, _growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
  have empty time : Worker.completed (trace.states time).services = none := by
    cases stored : Worker.completed (trace.states time).services with
    | none => rfl
    | some value =>
      have same := (kept time).services.safety.completed value stored
      exact False.elim (unfinished time (stored.trans (congrArg some same)))
  intro start
  let ready := max cut start
  obtain ⟨finishedAt, attempt, outcome, afterFinished, finished, correct⟩ :=
    iteration_returns whole supported comparable sameExit traversal enough trace initialized fair.workers
      ⟨0, nonempty⟩ ready (fun n beyond => noCrash 0 n (by dsimp [ready] at beyond; omega))
  have missing : outcome = none := by
    cases outcome with
    | none => rfl
    | some value =>
      obtain ⟨same, stored⟩ := correct value rfl
      exact False.elim (unfinished finishedAt (by simpa [same] using stored))
  subst outcome
  obtain ⟨iteratedAt, afterIteration, event⟩ := fair.iterate finishedAt 0 attempt _ finished rfl
  have executed := trace.execution iteratedAt
  simp only [event] at executed
  have active : ∃ generation, Continues ⟨0, generation⟩ (Program.ofEff (program traversal source))
      (trace.states (iteratedAt + 1)) := by
    generalize future : trace.states (iteratedAt + 1) = final at executed ⊢
    cases executed with
    | @iterate before worker generation value actual held found unfinished =>
      have same := (Array.mem_replicate.mp (Array.mem_of_getElem? found)).2
      subst actual
      exact ⟨generation, activate_continues _ _ _ (Array.getElem?_eq_some_iff.mp held).choose⟩
  obtain ⟨generation, active⟩ := active
  obtain ⟨dequeuedAt, call, reply, next, afterDequeue, event, saved⟩ := started_dequeues traversal source trace fair.workers
    empty (iteratedAt + 1) ⟨0, generation⟩ active (fun n beyond => noCrash 0 n (by dsimp [ready] at afterFinished; omega))
  exact ⟨dequeuedAt, call, ⟨0, generation⟩, reply, some next, by dsimp [ready] at afterFinished; omega, event, saved⟩

end LeanCloud.Backend.Proofs.Iteration
