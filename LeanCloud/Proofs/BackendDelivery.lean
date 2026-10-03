import LeanCloud.Proofs.BackendDeliveryCode

namespace LeanCloud.Backend.Proofs.Iteration
open Lean LeanEff LeanCloud.Proofs Execution

theorem callers (traversal : Nat) (source : Cloud Replay.M Json) (supported : PureProgram source)
    (trace : Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (program traversal source)))
    (time : Nat) : Linked (trace.states time) ∧ AllProtocol (polling traversal source) (trace.states time) := by
  have fresh (id : Nat) actual (found : (Array.replicate count (program traversal source))[id]? = some actual) :
      (Program.ofEff actual).protocol (polling traversal source) := by
    have same := (Array.mem_replicate.mp (Array.mem_of_getElem? found)).2
    subst actual
    exact protocol traversal source supported
  refine ⟨trace.linked (by rw [initialized]; exact initial_linked _ _) time,
    repeated_protocol trace fresh ?_ time⟩
  rw [initialized]
  exact initial_protocol _ _ fresh

/-- A live dequeue reply reaches the real step and publishes its handoff.
The caller and its code are proved from execution, not assumed by fairness. -/
theorem dequeue_publishes {source : Cloud Replay.M Json} {tree}
    (whole : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (traversal : Nat) (enough : sizeOf tree ≤ traversal)
    (trace : Trace traversal source count)
    (initialized : trace.states 0 = Execution.initial Replay.initial (Array.replicate count (program traversal source)))
    (fair : trace.schedule.WeaklyFair) (time id : Nat) (owner : Owner) (location : Location) (receipt : Receipt)
    (next : ArrsF Request (Option (Location × Receipt)) Outcome)
    (event : trace.events time = some (.action (.commit id)))
    (saved : (trace.states (time + 1)).calls[id]? = some (.committed owner .dequeue (some (location, receipt)) (some next)))
    (noCrash : trace.schedule.NoCrashesAfter owner.worker (time + 1)) :
    ∃ node, ∃ _route : TreeRoute tree Location.root location node,
      ∃ later response returned, time < later ∧
        (trace.states later).workers[owner.worker]? = some ⟨owner.attempt, .finished returned⟩ ∧
        Published tree location node (trace.states (time + 1)).services response (trace.states later).services ∧
        Post tree returned (trace.states later).services := by
  obtain ⟨kept, growth⟩ := certified whole supported comparable sameExit traversal enough trace initialized
  have performed := trace.schedule.execution time (.commit id) (by simp [Execution.Repeated.Trace.schedule, event])
  obtain ⟨issued, law⟩ := performed.commit_reply saved
  have selected := (Worker.dequeue_preserves (kept time).services.safety law).2.2 location receipt rfl
  obtain ⟨⟨node, route, active⟩, received⟩ := selected
  obtain ⟨linked, conforms⟩ := callers traversal source supported trace initialized (time + 1)
  have waiting := linked id _ saved owner rfl
  have code : Program.ofArrs next (some (location, receipt)) =
      Program.ofEff (dispatch traversal source (some (location, receipt))) :=
    (conforms id _ saved).1 _
  have safe := selected_checked whole supported route comparable (sameExit _ _ route.member)
    traversal (Nat.le_trans route.fuel_bound enough) receipt (trace.states (time + 1)).services
    (kept (time + 1)).services active received
  have safe : Safe (Accounting.Valid tree) Worker.Grows
      (fun actual final => ∃ outcome worker, actual = .ok (outcome, worker) ∧
        Returned tree outcome worker final ∧ ∃ response, Published tree location node (trace.states (time + 1)).services response final)
      (Program.ofArrs next (some (location, receipt))) (trace.states (time + 1)).services := by
    rw [code]
    exact safe
  obtain ⟨later, returned, beyond, finished, outcome, worker, same, correct, response, published⟩ :=
    Safe.responding_returns (grows := Worker.Grows) trace.schedule fair (fun a b => a.trans b)
      (fun time => (kept time).services) growth safe (time + 1) ⟨waiting, saved⟩ noCrash (.refl _)
  exact ⟨node, route, later, response, returned, by omega, finished, published, outcome, worker, same, correct⟩

end LeanCloud.Backend.Proofs.Iteration
