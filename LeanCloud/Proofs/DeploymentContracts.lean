import LeanCloud.Proofs.WorkerContracts
import LeanCloud.Proofs.SchedulerProgress
import LeanCloud.Proofs.SchedulerCompletion
import LeanCloud.Proofs.SchedulerRank

/-! The shared semantic invariant and mailbox contracts for actual deployment
actors. Scheduler state advances serially; workers preserve that private state
while creating immutable replay records. These predicates add no runtime state. -/

namespace LeanCloud.Proofs.DeploymentContracts
open Lean SimulationBackend ReplayModel SimulationLogic

structure Invariant (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (world : World) : Prop where
  records : Extends world.records expected
  assignments : SchedulerAssignments.Valid world.scheduler
  completed : SchedulerRecords.DoneRecords world.records world.scheduler.jobs
  groups : SchedulerGroups.Valid expected world.records world.scheduler.jobs
  paths : SchedulerPaths.Valid world.records encode program world.scheduler.jobs
  progress : SchedulerProgress.Valid world.scheduler.jobs
  unique : SchedulerRank.Unique world.scheduler.jobs
  messages : Traffic.Valid encode program expected world

theorem initial (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α) :
    Invariant expected encode program {} :=
  ⟨Extends.empty _, SchedulerAssignments.initial, SchedulerRecords.initial _, SchedulerGroups.initial _ _,
    SchedulerPaths.initial _ encode program, SchedulerProgress.initial, SchedulerRank.unique_initial,
    Traffic.initial encode program expected⟩

/-- Every job belongs to a branch of the original pure evaluation. Its key is
therefore in the finite source specification, even before its return is stored. -/
theorem Invariant.branch_keys {expected : Journal} {encode : α → Json} {program : Cloud (SimM World) α}
    {outcome world} (valid : Invariant expected encode program world)
    (meaning : Specification.Complete expected Location.root program outcome)
    (known : expected.lookup (ReplayStore.returnKey Location.root) =
      some ⟨ReplayStore.returnRequest, Parallel.recorded encode outcome⟩) :
    ∀ job ∈ world.scheduler.jobs, ReplayStore.returnKey job.branch ∈ expected.map Prod.fst := by
  intro job member
  obtain ⟨β, remainingEncode, remaining, steps, path⟩ := valid.paths job member
  obtain ⟨result, _, returned⟩ := meaning.resume (by simpa using known) path valid.records
  rw [← (valid.groups job member).branch] at returned
  have present : (expected.lookup (ReplayStore.returnKey job.branch)).isSome := by simp [returned]
  obtain ⟨entry, inside, same⟩ := List.lookup_isSome_iff.mp present
  exact List.mem_map.mpr ⟨entry, inside, (beq_iff_eq.mp same).symm⟩

private theorem Invariant.transport {expected : Journal} {encode : α → Json} {program : Cloud (SimM World) α}
    {before after : World} (valid : Invariant expected encode program before)
    (scheduler : after.scheduler = before.scheduler) (records : after.records = before.records)
    (messages : Traffic.Valid encode program expected after) : Invariant expected encode program after := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, messages⟩
  · simpa only [records] using valid.records
  · simpa only [scheduler] using valid.assignments
  · simpa only [scheduler, records] using valid.completed
  · simpa only [scheduler, records] using valid.groups
  · simpa only [scheduler, records] using valid.paths
  · simpa only [scheduler] using valid.progress
  · simpa only [scheduler] using valid.unique

theorem Invariant.network {expected : Journal} {encode : α → Json} {program : Cloud (SimM World) α}
    {world : World} (valid : Invariant expected encode program world) (event : NetworkEvent) :
    Invariant expected encode program (networkStep event world) :=
  valid.transport (SchedulerOwnership.network event world) (ReplayEvolution.network event world)
    (Traffic.network_preserves world event valid.messages)

theorem Invariant.disconnect {expected : Journal} {encode : α → Json} {program : Cloud (SimM World) α}
    {world : World} (valid : Invariant expected encode program world) (actor generation : Nat) :
    Invariant expected encode program (SimulationBackend.disconnect actor generation world) :=
  valid.transport (SchedulerOwnership.disconnect actor generation world) (ReplayEvolution.disconnect actor generation world)
    (Traffic.disconnect_preserves world actor generation valid.messages)

/-- Old attempts retain their identity, immutable records accumulate, and
completed jobs are never reopened or removed. -/
structure Advance (before after : World) : Prop where
  assignments : SchedulerAssignments.Forward before.scheduler after.scheduler
  records : Extends before.records after.records
  completed : SchedulerCompletion.Preserves before.scheduler.jobs after.scheduler.jobs
  rank : ∀ limit, SchedulerRank.rank limit before.scheduler.jobs ≤ SchedulerRank.rank limit after.scheduler.jobs

theorem Advance.refl (world : World) : Advance world world :=
  ⟨SchedulerAssignments.Forward.refl _, Extends.refl _, SchedulerCompletion.Preserves.refl _, fun _ => Nat.le_refl _⟩

theorem Advance.unchanged {before after : World}
    (scheduler : after.scheduler = before.scheduler) (records : after.records = before.records) :
    Advance before after :=
  ⟨by rw [scheduler]; exact .refl _, by rw [records]; exact .refl _, by rw [scheduler]; exact .refl _,
    fun _ => by rw [scheduler]; exact Nat.le_refl _⟩

theorem Advance.trans {first middle last : World} (earlier : Advance first middle) (later : Advance middle last) :
    Advance first last := ⟨earlier.assignments.trans later.assignments, earlier.records.trans later.records,
      earlier.completed.trans later.completed, fun limit => Nat.le_trans (earlier.rank limit) (later.rank limit)⟩

/-- Only the scheduler's local operations may change its private database.
Its pending local operations disappear on crash; remote orphan requests obey
the shared advance relation and cannot depend on exclusive process ownership. -/
def rules (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (scheduler : Bool) : Rules World where
  invariant := Invariant expected encode program
  interference before after := Advance before after ∧ (scheduler = true → after.scheduler = before.scheduler)
  orphanInterference := Advance
  guarantee remote before after := Advance before after ∧
    ((scheduler = true ∧ remote = false) ∨ after.scheduler = before.scheduler)

/-- The scheduler is actor zero. Every other actor and every remote orphan
preserves its private database, so these actor contracts satisfy the existing
simulator's interference-compatibility requirements. Startup contracts for the
complete loops must still be supplied before concluding trace safety. -/
def system (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (workers : Nat) : SimulationSafety.System World (workers + 1) where
  invariant := Invariant expected encode program
  evolution := Advance
  rely actor := (rules expected encode program (actor.val == 0)).interference
  guarantee actor := (rules expected encode program (actor.val == 0)).guarantee
  reflexive := Advance.refl
  transitive := Advance.trans
  compatible actor remote before after _ _ changes := by
    refine ⟨changes.1, fun other interfering => ⟨changes.1, ?_⟩⟩
    intro scheduler
    rcases changes.2 with owned | same
    · have sameActor : other = actor := Fin.ext (by
        have first : other.val = 0 := by simpa using scheduler
        have second : actor.val = 0 := by simpa using owned.1
        exact first.trans second.symm)
      rcases interfering with different | remote
      · exact False.elim (different sameActor)
      · simp_all
    · exact same

def WorkerReply (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (worker : WorkerId) (reply : Option (Received WorkerMessage)) (world : World) : Prop :=
  ∀ delivery, reply = some delivery →
    Traffic.ToWorker encode program expected world.scheduler world.records worker delivery.message

def SchedulerReply (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (reply : Option (Received SchedulerMessage)) (world : World) : Prop :=
  ∀ delivery, reply = some delivery →
    Traffic.ToScheduler encode program expected world.scheduler world.records delivery.message

/-- A delayed delivery retains assignment identity, readiness, and replay paths
through later scheduler transitions and concurrent record creation. -/
theorem worker_reply_stable (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (worker : WorkerId) (reply : Option (Received WorkerMessage)) :
    (rules expected encode program false).Stable (rules expected encode program false).interference
      (WorkerReply expected encode program worker reply) := by
  intro before after _ _ moves holds delivery found
  exact (holds delivery found).advance moves.1.1 moves.1.2

theorem scheduler_reply_stable (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (reply : Option (Received SchedulerMessage)) :
    (rules expected encode program true).Stable (rules expected encode program true).interference
      (SchedulerReply expected encode program reply) := by
  intro before after _ _ moves holds delivery found
  exact (holds delivery found).advance moves.1.1 moves.1.2

/-- The real simulated worker receive operation supplies the certificate needed
by its interpreter. Receiving reserves the durable message; it does not assume
that the message is new, or that its assignment is still live. -/
theorem worker_receive (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (worker : WorkerId) (generation : Nat) :
    (rules expected encode program false).Program (fun _ => True)
      (WorkerReply expected encode program worker) (workerPorts worker generation).inbox.receive := by
  apply Rules.send
  refine ⟨(fun _ _ _ _ _ _ => trivial), (fun _ _ _ _ _ _ _ => trivial),
    worker_reply_stable expected encode program worker, ?_⟩
  intro world invariant _
  have inbox := Traffic.inbox_valid invariant.messages worker
  refine ⟨?_, ⟨Advance.unchanged rfl rfl, Or.inr rfl⟩, fun delivery found => inbox.delivered generation delivery found⟩
  exact ⟨invariant.records, invariant.assignments, invariant.completed, invariant.groups, invariant.paths, invariant.progress, invariant.unique,
    ⟨invariant.messages.network, invariant.messages.scheduler,
      Traffic.update_workers invariant.messages worker _ (inbox.receive generation)⟩⟩

/-- Scheduler receipt preserves every global invariant and returns a message
whose report, if any, has durable completion backing and valid fork paths. -/
theorem scheduler_receive (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (generation : Nat) :
    (rules expected encode program true).Program (fun _ => True)
      (SchedulerReply expected encode program) (schedulerPorts generation).inbox.receive := by
  apply Rules.send
  refine ⟨(fun _ _ _ _ _ _ => trivial), (fun _ _ _ _ _ _ _ => trivial),
    scheduler_reply_stable expected encode program, ?_⟩
  intro world invariant _
  refine ⟨?_, ⟨Advance.unchanged rfl rfl, Or.inr rfl⟩,
    fun delivery found => invariant.messages.scheduler.delivered generation delivery found⟩
  exact ⟨invariant.records, invariant.assignments, invariant.completed, invariant.groups, invariant.paths, invariant.progress, invariant.unique,
    ⟨invariant.messages.network, invariant.messages.scheduler.receive generation, invariant.messages.workers⟩⟩

/-- Publication commits a certified worker report to durable transport. The
certificate survives even if this remote request commits after a process crash. -/
theorem worker_send (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (worker : WorkerId) (generation : Nat) (message : SchedulerMessage) :
    (rules expected encode program false).Program
      (fun world => Traffic.ToScheduler encode program expected world.scheduler world.records message)
      (fun _ world => Traffic.ToScheduler encode program expected world.scheduler world.records message)
      ((workerPorts worker generation).send message) := by
  apply Rules.send
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun _ _ _ _ moves valid => valid.advance moves.1.1 moves.1.2
  · exact fun _ _ _ _ _ moves valid => valid.advance moves.1 moves.2
  · exact fun _ _ _ _ _ moves valid => valid.advance moves.1.1 moves.1.2
  · intro world invariant valid
    exact ⟨⟨invariant.records, invariant.assignments, invariant.completed, invariant.groups, invariant.paths, invariant.progress, invariant.unique,
      Traffic.publish_preserves world (.scheduler message) invariant.messages valid⟩,
      ⟨Advance.unchanged rfl rfl, Or.inr rfl⟩, valid⟩

theorem scheduler_send (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (generation : Nat) (delivery : Delivery) :
    (rules expected encode program true).Program
      (fun world => Traffic.ToWorker encode program expected world.scheduler world.records delivery.worker delivery.message)
      (fun _ world => Traffic.ToWorker encode program expected world.scheduler world.records delivery.worker delivery.message)
      ((schedulerPorts generation).send delivery) := by
  apply Rules.send
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun _ _ _ _ moves valid => valid.advance moves.1.1 moves.1.2
  · exact fun _ _ _ _ _ moves valid => valid.advance moves.1 moves.2
  · exact fun _ _ _ _ _ moves valid => valid.advance moves.1.1 moves.1.2
  · intro world invariant valid
    exact ⟨⟨invariant.records, invariant.assignments, invariant.completed, invariant.groups, invariant.paths, invariant.progress, invariant.unique,
      Traffic.publish_preserves world (.worker delivery) invariant.messages valid⟩,
      ⟨Advance.unchanged rfl rfl, Or.inr rfl⟩, valid⟩

/-- Acknowledgement changes only broker ownership of the reserved message.
Session fencing, including acknowledgements from crashed processes, is handled
by the same mailbox model used by the actual operation. -/
theorem worker_acknowledge (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (worker : WorkerId) (generation receipt : Nat) :
    (rules expected encode program false).Program (fun _ => True) (fun _ _ => True)
      ((workerPorts worker generation).inbox.acknowledge receipt) := by
  apply Rules.send
  refine ⟨(fun _ _ _ _ _ _ => trivial), (fun _ _ _ _ _ _ _ => trivial),
    (fun _ _ _ _ _ _ _ => trivial), ?_⟩
  intro world invariant _
  refine ⟨?_, ⟨Advance.unchanged rfl rfl, Or.inr rfl⟩, trivial⟩
  exact ⟨invariant.records, invariant.assignments, invariant.completed, invariant.groups, invariant.paths, invariant.progress, invariant.unique,
    ⟨invariant.messages.network, invariant.messages.scheduler,
      Traffic.update_workers invariant.messages worker _
        ((Traffic.inbox_valid invariant.messages worker).acknowledge generation receipt)⟩⟩

theorem scheduler_acknowledge (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (generation receipt : Nat) :
    (rules expected encode program true).Program (fun _ => True) (fun _ _ => True)
      ((schedulerPorts generation).inbox.acknowledge receipt) := by
  apply Rules.send
  refine ⟨(fun _ _ _ _ _ _ => trivial), (fun _ _ _ _ _ _ _ => trivial),
    (fun _ _ _ _ _ _ _ => trivial), ?_⟩
  intro world invariant _
  refine ⟨?_, ⟨Advance.unchanged rfl rfl, Or.inr rfl⟩, trivial⟩
  exact ⟨invariant.records, invariant.assignments, invariant.completed, invariant.groups, invariant.paths, invariant.progress, invariant.unique,
    ⟨invariant.messages.network, invariant.messages.scheduler.acknowledge generation receipt, invariant.messages.workers⟩⟩

private theorem transport_preserves (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (workers : Nat) {post : Fin (workers + 1) → β → World → Prop}
    {state : Simulation.State World β (workers + 1)} {world : World}
    (valid : (system expected encode program workers).Valid post state)
    (postStable : ∀ actor value, ((system expected encode program workers).rules actor).Stable
      ((system expected encode program workers).rely actor) (post actor value))
    (invariant : Invariant expected encode program world)
    (scheduler : world.scheduler = state.world.scheduler) (records : world.records = state.world.records) :
    (system expected encode program workers).Valid post { state with world } ∧ Advance state.world world := by
  have moves : Advance state.world world := .unchanged scheduler records
  exact ⟨valid.advance _ postStable invariant moves (fun _ => ⟨moves, fun _ => scheduler⟩), moves⟩

/-- Once the actual actor starts meet these contracts, the combined invariant
and every saved reply assertion survive all actual process and network events.
This checks traces through the shared backend proof; it does not assume trace safety. -/
theorem trace_preserves (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (workers : Nat) (start : Simulation.Start World β (workers + 1))
    (post : Fin (workers + 1) → β → World → Prop)
    (postStable : ∀ actor value, ((system expected encode program workers).rules actor).Stable
      ((system expected encode program workers).rely actor) (post actor value))
    (starts : ∀ actor generation, ((system expected encode program workers).rules actor).Program
      (fun _ => True) (post actor) (start actor generation))
    {allowed : Simulation.Event (workers + 1) → Prop} {before after : Simulation.State World β (workers + 1)}
    (valid : (system expected encode program workers).Valid post before)
    (history : SchedulerOwnership.Trace start allowed before after) :
    (system expected encode program workers).Valid post after ∧ Advance before.world after.world :=
  (system expected encode program workers).backend_trace_preserves start post postStable starts
    (fun _ actor generation safe => transport_preserves expected encode program workers safe postStable
      (safe.invariant.disconnect actor generation) (SchedulerOwnership.disconnect _ _ _) (ReplayEvolution.disconnect _ _ _))
    (fun _ event safe => transport_preserves expected encode program workers safe postStable
      (safe.invariant.network event) (SchedulerOwnership.network _ _) (ReplayEvolution.network _ _)) valid history

end LeanCloud.Proofs.DeploymentContracts
