import LeanCloud.Proofs.BackendTermination

namespace LeanCloud.Backend.Proofs.Iteration
open Lean LeanEff LeanCloud.Proofs Execution

private theorem completed_safe (tree : ExecutionTree) (traversal : Nat) (source : Cloud Replay.M Json)
    (state : Backend.State) (stored : Worker.completed state = some (toJson tree.exit)) :
    ProgramSafe (Accounting.Valid tree) Worker.Grows
      (fun returned final => returned = .ok (.ok (some tree.exit), ⟨(), none⟩) ∧
        Worker.completed final = some (toJson tree.exit)) (program traversal source) state := by
  unfold ProgramSafe
  rw [normalized]
  apply Safe.request
  · intro current value after valid growth law
    obtain ⟨_, rfl⟩ := law
    exact ⟨valid, .refl _⟩
  · intro current value after valid growth law
    obtain ⟨same, rfl⟩ := law
    have present := growth.completed _ stored
    have valueEq : value = some (toJson tree.exit) := same.trans present
    subst value
    rw [valueEq]
    simp only [exit_roundtrip]
    exact .pure fun final bounded later => ⟨rfl, later.completed _ present⟩

/-- Every surviving worker eventually observes the durable result. An old
unfinished iteration may finish first; fair repetition then performs the real
completion read and returns that outcome. -/
theorem eventually_returns {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (program traversal source)))
    (fair : trace.WeaklyFair) (deliveries : trace.FairDelivery)
    (worker : Fin count) (cut : Nat) (noCrash : ∀ worker, trace.schedule.NoCrashesAfter worker cut) :
    ∃ later attempt, cut ≤ later ∧
      (trace.states later).workers[worker.val]? = some ⟨attempt, .finished (.ok (.ok (some tree.exit), ⟨(), none⟩))⟩ ∧
      Worker.completed (trace.states later).services = some (toJson tree.exit) := by
  have nonempty : 0 < count := Nat.lt_of_le_of_lt (Nat.zero_le worker.val) worker.isLt
  obtain ⟨completedAt, recorded⟩ := eventually_completed whole supported comparable sameExit traversal enough trace initialized deliveries fair nonempty cut noCrash
  obtain ⟨kept, growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
  let ready := max cut completedAt
  obtain ⟨first, attempt, outcome, afterFirst, finished, correct⟩ := iteration_returns whole supported comparable sameExit
    traversal enough trace initialized fair.workers worker ready
      (fun n beyond => noCrash worker n (by dsimp [ready] at beyond; omega))
  cases outcome with
  | some value =>
    obtain ⟨rfl, stored⟩ := correct value rfl
    exact ⟨first, attempt, by dsimp [ready] at afterFirst; omega, finished, stored⟩
  | none =>
    obtain ⟨iteratedAt, afterIteration, event⟩ := fair.iterate first worker attempt _ finished rfl
    have executed := trace.execution iteratedAt
    simp only [event] at executed
    have active : ∃ generation, Continues ⟨worker, generation⟩ (Program.ofEff (program traversal source))
        (trace.states (iteratedAt + 1)) := by
      generalize future : trace.states (iteratedAt + 1) = final at executed ⊢
      cases executed with
      | @iterate before worker generation value actual held found unfinished =>
        have same := (Array.mem_replicate.mp (Array.mem_of_getElem? found)).2
        subst actual
        exact ⟨generation, activate_continues _ _ _ (Array.getElem?_eq_some_iff.mp held).choose⟩
    obtain ⟨generation, active⟩ := active
    have present := (growth completedAt (iteratedAt + 1) (by dsimp [ready] at afterFirst; omega)).completed _ recorded
    obtain ⟨later, returned, beyond, finished, equal, stored⟩ := Safe.eventually_returns (grows := Worker.Grows)
      trace.schedule fair.workers (fun a b => a.trans b) (fun n => (kept n).services) growth
      (completed_safe tree traversal source _ present) (iteratedAt + 1) active
      (fun n beyond => noCrash worker n (by dsimp [ready] at afterFirst; omega)) (.refl _)
    subst returned
    exact ⟨later, generation, by dsimp [ready] at afterFirst; omega, finished, stored⟩

end LeanCloud.Backend.Proofs.Iteration
