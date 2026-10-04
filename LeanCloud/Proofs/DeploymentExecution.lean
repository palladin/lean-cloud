import LeanCloud.Proofs.SchedulerOwnership
import LeanCloud.Proofs.SimulationProgress

/-! Execution of an existing worker computation inside a deployment trace.
Other actors and the broker may run between its atomic operations. The relation
records operations and their actual before/after states, not successful results.
An uninterrupted segment is the existing finite SimM execution relation. -/

namespace LeanCloud.Proofs.DeploymentExecution
open LeanEff SimulationBackend SimulationLogic

variable {info : Option Empty}

private abbrev Trace (actors : Simulation.Start World Unit count) :=
  SchedulerOwnership.Trace actors (fun _ => True)

inductive Execution (actors : Simulation.Start World Unit count) :
    SimM World α → Simulation.State World Unit count → α →
      Simulation.State World Unit count → Prop where
  | uninterrupted (executed : SimulationProgress.Execution program before.world value after.world operations)
      (history : Trace actors before after) : Execution actors program before value after
  | step {info : Option Empty} (remote : Bool) (label : String) (operation : World → β × World)
      (next : ArrsF (Atomic World) Empty β α)
      (waiting : Trace actors before ready)
      (committed : Trace actors ready saved)
      (effect : saved.world = (operation ready.world).2)
      (rest : Execution actors (next.apply (operation ready.world).1) saved value after) :
      Execution actors (.impure info (.step remote label operation) next) before value after

theorem Execution.trace {actors : Simulation.Start World Unit count}
    (executed : Execution actors program before value after) : Trace actors before after := by
  induction executed with
  | uninterrupted _ history => exact history
  | step _ _ _ _ waiting committed _ _ ih => exact (waiting.trans committed).trans ih

/-- Stable operation contracts remain true during the actual intervening
deployment events. Reachability supplies their invariant and interference laws;
neither the environment nor this relation assumes the final postcondition. -/
theorem Execution.post {actors : Simulation.Start World Unit count}
    (rules : Rules World) (initial : Simulation.State World Unit count)
    (invariant : ∀ state, Trace actors initial state → rules.invariant state.world)
    (interference : ∀ before after, Trace actors initial before → Trace actors before after →
      rules.interference before.world after.world)
    {program : SimM World α} {before after} {value}
    (executed : Execution actors program before value after)
    {pre : World → Prop} {post : α → World → Prop}
    (valid : rules.Program pre post program)
    (history : Trace actors initial before) (holds : pre before.world) : post value after.world :=
  match executed with
  | .uninterrupted segment _ => (segment.post rules valid (invariant before history) holds).2
  | .step _ _ _ next waiting committed effect rest => by
    obtain ⟨required, reply, entails, operation, continuation⟩ := valid
    have readyHistory := history.trans waiting
    have needed := operation.waiting _ _ (invariant _ history) (invariant _ readyHistory)
      (interference _ _ history waiting) (entails _ (invariant _ history) holds)
    have replied := (operation.execute _ (invariant _ readyHistory) needed).2.2
    rw [← effect] at replied
    exact rest.post rules initial invariant interference (Rules.apply rules next continuation _)
      (readyHistory.trans committed) replied
termination_by structural executed

end LeanCloud.Proofs.DeploymentExecution
