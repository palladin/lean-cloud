import LeanCloud.Proofs.ConcurrentStep
import LeanCloud.Proofs.ReplayRelation

/-! The actual leased Db adapter preserves the atomic behavior of a replay
step and carries its delivery receipt unchanged. -/

namespace LeanCloud.Proofs.LeasedStep
open Lean LeanEff Simulation

private def relation (db : Db σ (SimM δ)) : ReplayRelation db (LeaseQueue.db (ρ := ρ) db) where
  relates := WithHandle
  pure := WithHandle.pure
  throw := WithHandle.throw
  bind := WithHandle.bind
  get key := WithHandle.lift (db.get key)
  put key value := WithHandle.lift (db.put key value)

theorem step (db : Db σ (SimM δ)) (blobs : BlobStorage σ (SimM δ))
    (leasedBlobs : BlobStorage (LeaseQueue.Worker σ ρ) (SimM δ)) (fuel : Nat)
    (program : Cloud (SimM δ) Json) (supported : PureProgram program) (location : Location) :
    WithHandle (ReplayInterpreter.Internal.step db blobs fuel program location)
      (ReplayInterpreter.Internal.step (LeaseQueue.db db) leasedBlobs fuel program location) :=
  (relation db).step blobs leasedBlobs fuel program supported location

end LeanCloud.Proofs.LeasedStep

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean LeanEff Simulation SimulationBackend JournalDb JournalAdapter ReplayRecovery

/-- Reuse a journal-action proof with the worker's real local receipt. -/
theorem Checked.leased {expected : Journal}
    {action : ExceptT CloudError (StateT Unit M) α}
    {leased : ExceptT CloudError (StateT SimulationBackend.Worker M) α}
    {post : α → Durable → Prop} {state : Durable}
    (safe : Checked expected action post state) (valid : Valid expected state)
    (stable : ∀ value before after, Grows before after → post value before → post value after)
    (same : WithHandle action leased) (worker : SimulationBackend.Worker) :
    Safe (Valid expected) Grows
      (fun returned final => ∃ value, returned = (.ok value, worker) ∧ post value final)
      (.ofProgram (leased.run worker)) state := by
  apply Safe.equivalent Grows.refl (fun first second => first.trans second)
    (first := LeaseQueue.liftBackend action.run worker) (kept := valid) (same := same worker)
  cases worker with
  | mk backend delivery =>
    cases backend
    apply Safe.bind Grows.refl (fun first second => first.trans second) safe valid
    intro returned current kept done
    obtain ⟨value, rfl, result⟩ := done
    exact .finished fun final bounded growth => ⟨value, rfl, stable value current final growth result⟩

theorem Emits.grow {tree response before after} (emitted : Emits tree response before)
    (growth : Grows before after) : Emits tree response after := by
  cases response with
  | done outcome => exact emitted
  | runnable locations => exact fun location member => (emitted location member).grow growth.1

/-- The public step with the actual simulation backend and lease receipt.
Receipt state survives execution unchanged; journal safety and original-program
responses remain valid across all intervening atomic operations and replies. -/
theorem leased_step_checked {program : Cloud M Json} {tree current node}
    (whole : Expansion program tree) (supported : PureProgram program)
    (route : TreeRoute tree Location.root current node)
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : (node.exit == node.exit) = true)
    (state : Durable) (valid : Valid (tree.journal Location.root) state)
    (active : route.Activated (view state)) (fuel : Nat) (enough : route.prefixSteps + 1 ≤ fuel)
    (worker : SimulationBackend.Worker) :
    Safe (Valid (tree.journal Location.root)) Grows
      (fun returned final => ∃ response, returned = (.ok response, worker) ∧ Emits tree response final ∧
        StepProgress tree current node state response final)
      (.ofProgram ((ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs fuel program current).run worker)) state := by
  let blobs : BlobStorage Unit M := {
    putBlob := fun _ => throw ⟨.unsupported, "Unused in pure programs"⟩
    readBlob := fun _ => throw ⟨.unsupported, "Unused in pure programs"⟩
    resolveBlob := fun _ => throw ⟨.unsupported, "Unused in pure programs"⟩ }
  exact (step_progress whole supported route comparable sameExit blobs state valid active fuel enough).leased valid
    (fun _ _ _ growth h => ⟨h.1.grow growth, h.2.grow (.refl _) growth⟩)
    (LeasedStep.step (JournalDb.ofDb rawDb) blobs SimulationBackend.noBlobs fuel program supported current) worker

end LeanCloud.Proofs.ConcurrentJournal
