import LeanCloud.Proofs.ConcurrentQueue
import LeanCloud.Proofs.ReplayFootprint

/-! Compose journal execution with the actual leased queue adapter. A step's
own requests affect only journal records, so its safety proof also preserves
the meaning of retained queue messages and the published final outcome. -/

namespace LeanCloud.Proofs.ConcurrentQueue
open Lean LeanEff Simulation SimulationBackend ReplayRecovery

private theorem journal_commit {tree : ExecutionTree} {operation : Durable → α × Durable}
    (only : ReplayFootprint.JournalOnly operation) (state : Durable) (valid : Valid tree state)
    (kept : ConcurrentJournal.Valid (tree.journal Location.root) (operation state).2)
    (growth : ConcurrentJournal.Grows state (operation state).2) :
    Valid tree (operation state).2 ∧ Grows state (operation state).2 := by
  obtain ⟨transport, completed⟩ := only state
  refine ⟨⟨kept, ?_, ?_⟩, growth, ?_⟩
  · intro index message stored
    rw [transport] at stored
    exact (valid.pending index message stored).grow growth.1
  · intro outcome stored
    exact valid.completed outcome (completed.symm.trans stored)
  · intro outcome stored
    exact completed.trans stored

/-- The actual replay step preserves the joint journal/queue invariant under
interleaving, including a stale delivery whose ancestor has already completed. -/
theorem step_safe {program : Cloud M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root)) (sameExit : (node.exit == node.exit) = true)
    (state : Durable) (valid : Valid tree state)
    (active : route.Activated (ConcurrentJournal.view state)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel)
    (worker : SimulationBackend.Worker) :
    Safe (Valid tree) Grows
      (fun returned final => ∃ response, returned = (.ok response, worker) ∧ ConcurrentJournal.Emits tree response final ∧
        ConcurrentJournal.StepProgress tree current node state response final)
      (.ofProgram ((ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs fuel program current).run worker)) state := by
  apply (ConcurrentJournal.leased_step_checked whole supported route comparable sameExit state valid.journal
    active fuel enough worker).refine ConcurrentJournal.Grows.refl (fun a b => a.trans b) valid.journal
      ReplayFootprint.JournalOnly (ReplayFootprint.step fuel program supported current worker)
      (fun _ h => h.journal) (fun h => h.journal)
  exact fun operation only current kept grown extended => journal_commit only current kept grown extended

end LeanCloud.Proofs.ConcurrentQueue
