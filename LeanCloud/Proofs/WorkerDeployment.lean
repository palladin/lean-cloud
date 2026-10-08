import LeanCloud.Proofs.DeploymentContracts
import LeanCloud.Proofs.SimulationRefinement

/-! Lift the existing worker execution proof into the shared deployment
invariant. Replay operations preserve coordination fields, and correct immutable
record growth preserves scheduler metadata and outstanding message certificates. -/

namespace LeanCloud.Proofs.WorkerDeployment
open Lean SimulationBackend ReplayModel SimulationLogic DeploymentContracts

private theorem replay_preserves {expected : Journal} {encode : α → Json} {program : Cloud (SimM World) α}
    {before after : World} (valid : Invariant expected encode program before)
    (correct : Extends after.records expected) (grows : Extends before.records after.records)
    (same : ReplayContracts.PreservesCoordination before after) : Invariant expected encode program after := by
  refine ⟨correct, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [same.scheduler] using valid.assignments
  · simpa only [same.scheduler] using valid.completed.extend grows
  · simpa only [same.scheduler] using valid.groups.extend grows
  · simpa only [same.scheduler] using valid.paths.extend grows
  · simpa only [same.scheduler] using valid.progress
  · simpa only [same.scheduler] using valid.unique
  · have messages := valid.messages.advance before.scheduler after.records (SchedulerAssignments.Forward.refl _) grows
    constructor
    · simpa only [same.scheduler, same.network] using messages.network
    · simpa only [same.scheduler, same.schedulerInbox] using messages.scheduler
    · simpa only [same.scheduler, same.workerInboxes] using messages.workers

/-- The storage guarantee is enough to reuse the whole replay proof in the
deployment system. Arbitrary interfering user IO is not assumed to satisfy it;
the worker theorem applies to the supported pure source specification. -/
theorem refinement (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α) :
    Refinement (ReplayContracts.rules expected) (rules expected encode program false) := by
  refine ⟨(fun _ invariant => invariant.records), (fun _ _ moves => moves.1.2),
    (fun _ _ moves => moves.2), ?_⟩
  intro remote before after invariant correct changes
  refine ⟨replay_preserves invariant correct changes.1 changes.2, ?_⟩
  exact ⟨⟨by rw [changes.2.scheduler]; exact .refl _, changes.1,
    by rw [changes.2.scheduler]; exact .refl _, fun _ => by rw [changes.2.scheduler]; exact Nat.le_refl _⟩, Or.inr changes.2.scheduler⟩

/-- A received assignment produces a report ready for durable publication.
The assignment's historical identity remains valid while execution is suspended,
including after timeout or reassignment by the scheduler. -/
theorem execute [codec : Codec α] (expected : Journal) (worker : WorkerId) (assignment : Assignment)
    (fuel : Nat) (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩) :
    (rules expected codec.encode (program input) false).Program
      (fun world => Traffic.ToWorker codec.encode (program input) expected world.scheduler world.records worker (.execute assignment))
      (fun report world => Traffic.ToScheduler codec.encode (program input) expected world.scheduler world.records (.report report))
      (LeanCloud.Worker.execute worker (observed worker) blobs fuel program input assignment) := by
  apply Rules.Program.exists_pre
  intro point
  apply Rules.Program.assuming
  intro same
  subst assignment
  have execution := (refinement expected codec.encode (program input)).program _
    (WorkerContracts.assigned expected worker point fuel program input meaning known)
  have identity : (rules expected codec.encode (program input) false).Frame
      (fun world => SchedulerAssignments.Identifies world.scheduler worker point) :=
    ⟨(fun _ _ _ _ moves holds => holds.advance moves.1.1),
      (fun _ _ _ _ moves holds => holds.advance moves.1),
      (fun _ _ _ _ _ moves holds => holds.advance moves.1.1)⟩
  apply Rules.Program.weaken
  · apply Rules.Program.weaken_post _ _ (execution.frame _ _ identity)
    intro report world invariant holds
    obtain ⟨returned, known, result⟩ := holds.1
    exact result.to_scheduler holds.2
  · exact fun _ _ valid => ⟨valid.2, valid.1⟩

/-- The actual worker turn receives a certified assignment, executes it,
publishes a certified report, and only then acknowledges its delivery. Polling
and terminal messages obey the same shared invariant. -/
theorem turn [codec : Codec α] (expected : Journal) (worker : WorkerId) (generation fuel : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (state : LeanCloud.Worker.State) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩) :
    (rules expected codec.encode (program input) false).Program (fun _ => True) (fun _ _ => True)
      (LeanCloud.Worker.turn (workerPorts worker generation) fuel program input state) := by
  unfold LeanCloud.Worker.turn
  split
  · exact fun _ _ _ => trivial
  · apply Rules.bind _ (worker_receive expected codec.encode (program input) worker generation)
    intro received
    cases received with
    | none =>
      dsimp only
      split
      · apply Rules.bind _ ((worker_send expected codec.encode (program input) worker generation (.ready worker)).weaken _
          (fun _ _ _ => trivial))
        intro _
        exact fun _ _ _ => trivial
      · exact fun _ _ _ => trivial
    | some delivery =>
      rcases delivery with ⟨receipt, message⟩
      dsimp only
      cases message <;> dsimp only
      case execute assignment =>
        apply Rules.Program.weaken (required := fun world => Traffic.ToWorker codec.encode (program input) expected
          world.scheduler world.records worker (.execute assignment))
        · apply Rules.bind _ (execute expected worker assignment fuel program input meaning known)
          intro report
          apply Rules.bind _ (worker_send expected codec.encode (program input) worker generation (.report report))
          intro _
          repeat first
            | exact fun _ _ _ => trivial
            | apply Rules.bind _ ((worker_send expected codec.encode (program input) worker generation (.ready worker)).weaken _
                (fun _ _ _ => trivial))
            | apply Rules.bind _ ((worker_acknowledge expected codec.encode (program input) worker generation receipt).weaken _
                (fun _ _ _ => trivial))
            | intro _
            | split
        · exact fun _ _ valid => valid ⟨receipt, .execute assignment⟩ rfl
      all_goals repeat first
        | exact fun _ _ _ => trivial
        | apply Rules.bind _ ((worker_send expected codec.encode (program input) worker generation (.ready worker)).weaken _
            (fun _ _ _ => trivial))
        | apply Rules.bind _ ((worker_acknowledge expected codec.encode (program input) worker generation receipt).weaken _
            (fun _ _ _ => trivial))
        | intro _
        | split

theorem loop [codec : Codec α] (expected : Journal) (worker : WorkerId) (turns generation fuel : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (state : LeanCloud.Worker.State) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩) :
    (rules expected codec.encode (program input) false).Program (fun _ => True) (fun _ _ => True)
      (workerLoop turns fuel (workerPorts worker generation) program input state) := by
  induction turns generalizing state with
  | zero => exact fun _ _ _ => trivial
  | succ turns ih =>
    apply Rules.bind _ (turn expected worker generation fuel program input state meaning known)
    intro next
    split
    · exact ih next
    · exact fun _ _ _ => trivial

/-- Every actual worker startup and restart reconnects its durable mailbox and
enters the certified loop. No execution or message-validity premise is left to
the caller beyond the meaning of the original pure source program. -/
theorem startup [codec : Codec α] (expected : Journal) (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) {outcome}
    (meaning : Specification.Complete expected Location.root (program input) outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩)
    (actor : Fin (workers + 1)) (worker : actor.val ≠ 0) (generation : Nat) :
    (rules expected codec.encode (program input) false).Program (fun _ => True) (fun _ _ => True)
      (SimulationBackend.start turns fuel duration program input actor generation) := by
  unfold SimulationBackend.start
  simp only [beq_eq_false_iff_ne.mpr worker, Bool.false_eq_true, ite_false]
  apply Rules.bind
  · apply Rules.send
    refine ⟨(fun _ _ _ _ _ _ => trivial), (fun _ _ _ _ _ _ _ => trivial),
      (fun _ _ _ _ _ _ _ => trivial), ?_⟩
    intro world invariant _
    exact ⟨⟨invariant.records, invariant.assignments, invariant.completed, invariant.groups, invariant.paths, invariant.progress, invariant.unique,
      ⟨invariant.messages.network, invariant.messages.scheduler, Traffic.update_workers invariant.messages _ _
        ((Traffic.inbox_valid invariant.messages _).connect generation)⟩⟩,
      ⟨Advance.unchanged rfl rfl, Or.inr rfl⟩, trivial⟩
  · intro _
    exact loop expected _ turns generation fuel program input {} meaning known

end LeanCloud.Proofs.WorkerDeployment
