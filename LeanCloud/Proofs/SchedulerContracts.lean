import LeanCloud.Proofs.DeploymentContracts

/-! The actual scheduler's private load/save protocol under the shared
deployment invariant. Local requests cannot outlive a crashed process. -/

namespace LeanCloud.Proofs.SchedulerContracts
open Lean SimulationBackend ReplayModel SimulationLogic DeploymentContracts

theorem load (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (generation : Nat) (pre : World → Prop)
    (stable : (rules expected encode program true).Stable (rules expected encode program true).interference pre) :
    (rules expected encode program true).Program pre
      (fun state world => state = world.scheduler ∧ pre world) (schedulerPorts generation).localDb.load := by
  apply Rules.send
  refine ⟨stable, (by intro impossible; cases impossible), ?_, ?_⟩
  · intro state before after first last moves holds
    exact ⟨holds.1.trans (moves.2 rfl).symm, stable before after first last moves holds.2⟩
  · intro world invariant holds
    exact ⟨invariant, ⟨Advance.unchanged rfl rfl, Or.inr rfl⟩, rfl, holds⟩

/-- Saving a value derived from the latest load is safe because other actors
cannot change this private database. A crash abandons this local pending save. -/
theorem save (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (generation : Nat) (before after : Scheduler.State) (pre post : World → Prop)
    (preStable : (rules expected encode program true).Stable (rules expected encode program true).interference pre)
    (postStable : (rules expected encode program true).Stable (rules expected encode program true).interference post)
    (changes : ∀ world, Invariant expected encode program world → before = world.scheduler → pre world →
      Invariant expected encode program { world with scheduler := after } ∧
      Advance world { world with scheduler := after } ∧ post { world with scheduler := after }) :
    (rules expected encode program true).Program (fun world => before = world.scheduler ∧ pre world)
      (fun _ => post) ((schedulerPorts generation).localDb.save after) := by
  apply Rules.send
  refine ⟨?_, (by intro impossible; cases impossible), fun _ => postStable, ?_⟩
  · intro first last firstValid lastValid moves holds
    exact ⟨holds.1.trans (moves.2 rfl).symm, preStable first last firstValid lastValid moves holds.2⟩
  · intro world invariant holds
    obtain ⟨preserved, advanced, result⟩ := changes world invariant holds.1 holds.2
    exact ⟨preserved, ⟨advanced, Or.inl ⟨rfl, rfl⟩⟩, result⟩

private theorem handle (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (world : World) (duration : Nat) (message : SchedulerMessage)
    (invariant : Invariant expected encode program world)
    (valid : Traffic.ToScheduler encode program expected world.scheduler world.records message) :
    Invariant expected encode program { world with scheduler := (Scheduler.handle duration world.scheduler message).1 } ∧
      Advance world { world with scheduler := (Scheduler.handle duration world.scheduler message).1 } ∧
      ∀ delivery ∈ (Scheduler.handle duration world.scheduler message).2,
        Traffic.ToWorker encode program expected (Scheduler.handle duration world.scheduler message).1
          world.records delivery.worker delivery.message := by
  have backed : SchedulerRecords.MessageBacked world.records world.scheduler message := by
    cases message <;> first | exact valid.2.1 | trivial
  have forked : match (generalizing := false) message with
      | .report report => SchedulerRecords.ForkBacked expected world.scheduler report | _ => True := by
    cases message <;> first | exact valid.2.2.1 | trivial
  have paths : match (generalizing := false) message with
      | .report report => Suspension.ReportPaths world.records encode program report | _ => True := by
    cases message <;> first | exact valid.2.2.2.1 | trivial
  obtain ⟨assignments, forward⟩ := SchedulerAssignments.handle_preserves world.scheduler duration message invariant.assignments
  exact ⟨⟨invariant.records, assignments,
    SchedulerRecords.handle_preserves _ _ _ _ invariant.completed backed,
    SchedulerGroups.handle_preserves _ _ _ _ _ invariant.groups invariant.completed invariant.records backed forked,
    SchedulerPaths.handle_preserves _ _ _ _ invariant.paths paths,
    SchedulerProgress.handle_preserves _ _ _ expected invariant.progress forked,
    SchedulerRank.unique_handle world.scheduler duration message invariant.unique,
    invariant.messages.advance _ _ forward (Extends.refl _)⟩,
    ⟨forward, Extends.refl _, SchedulerCompletion.handle world.scheduler duration message,
      fun limit => SchedulerRank.handle limit world.scheduler duration message expected world.records encode program invariant.groups valid⟩,
    Traffic.scheduler_sends_valid _ _ _ _ _ invariant.assignments invariant.groups invariant.paths⟩

def Outgoing (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (deliveries : Array Delivery) (world : World) : Prop :=
  ∀ delivery ∈ deliveries, Traffic.ToWorker encode program expected world.scheduler world.records delivery.worker delivery.message

private theorem outgoing_frame (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (deliveries : Array Delivery) : (rules expected encode program true).Frame (Outgoing expected encode program deliveries) := by
  constructor
  · exact fun _ _ _ _ moves valid delivery member => (valid delivery member).advance moves.1.1 moves.1.2
  · exact fun _ _ _ _ moves valid delivery member => (valid delivery member).advance moves.1 moves.2
  · exact fun _ _ _ _ _ moves valid delivery member => (valid delivery member).advance moves.1.1 moves.1.2

theorem save_handled (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (generation duration : Nat) (state : Scheduler.State) (message : SchedulerMessage) :
    (rules expected encode program true).Program
      (fun world => state = world.scheduler ∧ Traffic.ToScheduler encode program expected world.scheduler world.records message)
      (fun _ => Outgoing expected encode program (Scheduler.handle duration state message).2)
      ((schedulerPorts generation).localDb.save (Scheduler.handle duration state message).1) := by
  apply save expected encode program generation state _ _ _
    (fun _ _ _ _ moves valid => valid.advance moves.1.1 moves.1.2)
    (outgoing_frame expected encode program _).interference
  intro world invariant same valid
  subst state
  exact handle expected encode program world duration message invariant valid

/-- The deployed scheduler turn keeps all shared invariants while processing a
message, persisting the new state, publishing replies, and acknowledging input. -/
theorem turn (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (generation duration : Nat) :
    (rules expected encode program true).Program (fun _ => True) (fun _ _ => True)
      (Scheduler.turn (schedulerPorts generation) duration) := by
  unfold Scheduler.turn
  apply Rules.bind _ (scheduler_receive expected encode program generation)
  intro received
  cases received with
  | none => exact fun _ _ _ => trivial
  | some delivery =>
    apply Rules.Program.weaken (required := fun world =>
      Traffic.ToScheduler encode program expected world.scheduler world.records delivery.message)
    · apply Rules.bind _ (load expected encode program generation _
        (fun _ _ _ _ moves valid => valid.advance moves.1.1 moves.1.2))
      intro state
      apply Rules.bind _ (save_handled expected encode program generation duration state delivery.message)
      intro _
      apply Rules.bind
      · apply Rules.forIn_array
        intro outgoing member accumulator
        apply Rules.bind
        · apply Rules.Program.weaken
          · apply Rules.Program.weaken_post _ _ ((scheduler_send expected encode program generation outgoing).frame _ _
              (outgoing_frame expected encode program (Scheduler.handle duration state delivery.message).2))
            exact fun _ _ _ holds => holds.2
          · exact fun _ _ valid => ⟨valid outgoing member, valid⟩
        · intro _
          exact fun _ _ holds => holds
      · intro _
        exact (scheduler_acknowledge expected encode program generation delivery.receipt).weaken _ (fun _ _ _ => trivial)
    · exact fun _ _ valid => valid delivery rfl

theorem save_recovered (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (generation : Nat) (state : Scheduler.State) :
    (rules expected encode program true).Program (fun world => state = world.scheduler ∧ True) (fun _ _ => True)
      ((schedulerPorts generation).localDb.save (Recovery.recovered state)) := by
  apply save expected encode program generation state _ (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
  intro world invariant same _
  subst state
  obtain ⟨assignments, forward⟩ := SchedulerAssignments.recover_preserves world.scheduler invariant.assignments
  exact ⟨⟨invariant.records, assignments,
    SchedulerRecords.recover_preserves _ _ invariant.completed,
    SchedulerGroups.recover_preserves _ _ _ invariant.groups,
    SchedulerPaths.recover_preserves _ _ invariant.paths,
    SchedulerProgress.recover_preserves _ invariant.progress,
    SchedulerRank.unique_recover world.scheduler invariant.unique,
    invariant.messages.advance _ _ forward (Extends.refl _)⟩,
    ⟨forward, Extends.refl _, SchedulerCompletion.recover world.scheduler, fun limit => SchedulerRank.recover limit world.scheduler⟩, trivial⟩

/-- Recovery uses the same private load/save protocol and preserves every
shared invariant while releasing assignments held by previous processes. -/
theorem recover (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (generation : Nat) :
    (rules expected encode program true).Program (fun _ => True) (fun _ _ => True)
      (Scheduler.recover (schedulerPorts generation).localDb) := by
  apply Rules.bind _ (load expected encode program generation (fun _ => True) (fun _ _ _ _ _ _ => trivial))
  intro state
  exact save_recovered expected encode program generation state

theorem loop (expected : Journal) (encode : α → Json) (program : Cloud (SimM World) α)
    (turns duration generation : Nat) :
    (rules expected encode program true).Program (fun _ => True) (fun _ _ => True)
      (schedulerLoop turns duration generation) := by
  induction turns with
  | zero => exact fun _ _ _ => trivial
  | succ turns ih => exact Rules.bind _ (turn expected encode program generation duration) (fun _ => ih)

/-- The scheduler's actual startup, including durable inbox reconnection,
private database recovery, and its mailbox loop, satisfies the shared contract.
The result holds for every restart generation and every loop budget. -/
theorem startup [codec : Codec α] (expected : Journal) (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (generation : Nat) :
    (rules expected codec.encode (program input) true).Program (fun _ => True) (fun _ _ => True)
      (SimulationBackend.start (workers := workers) turns fuel duration program input
        ⟨0, Nat.zero_lt_succ workers⟩ generation) := by
  unfold SimulationBackend.start
  simp only [beq_self_eq_true, ite_true]
  apply Rules.bind
  · apply Rules.send
    refine ⟨(fun _ _ _ _ _ _ => trivial), (fun _ _ _ _ _ _ _ => trivial),
      (fun _ _ _ _ _ _ _ => trivial), ?_⟩
    intro world invariant _
    exact ⟨⟨invariant.records, invariant.assignments, invariant.completed, invariant.groups, invariant.paths, invariant.progress, invariant.unique,
      ⟨invariant.messages.network, invariant.messages.scheduler.connect generation, invariant.messages.workers⟩⟩,
      ⟨Advance.unchanged rfl rfl, Or.inr rfl⟩, trivial⟩
  · intro _
    exact Rules.bind _ (recover expected codec.encode (program input) generation)
      (fun _ => loop expected codec.encode (program input) turns duration generation)

end LeanCloud.Proofs.SchedulerContracts
