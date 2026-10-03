import LeanCloud.Proofs.SchedulerContracts
import LeanCloud.Proofs.SimulationProgress

/-! An uninterrupted scheduler turn processes an actual durable mailbox
delivery, saves its transition, confirms its replies, and acknowledges input.
These statements concern the deployed turn and the existing Sim ports. -/

namespace LeanCloud.Proofs.SchedulerDelivery
open LeanEff SimulationBackend SimulationProgress

private theorem send_all (generation : Nat) (deliveries : Array Delivery) (world : World) :
    Execution (forIn deliveries PUnit.unit fun delivery _ => do
      (schedulerPorts generation).send delivery
      pure (ForInStep.yield PUnit.unit)) world PUnit.unit
      { world with network := world.network ++ deliveries.map Envelope.worker } deliveries.size := by
  rw [← Array.forIn_toList]
  generalize itemsEq : deliveries.toList = items
  have same : deliveries = items.toArray := by simpa using congrArg List.toArray itemsEq
  subst deliveries
  clear itemsEq
  induction items generalizing world with
  | nil => simpa using! Execution.pure PUnit.unit world
  | cons delivery rest ih =>
    rw [List.forIn_cons]
    have sent := Execution.send true "scheduler.send"
      (fun world : World => ((), { world with network := world.network.push (.worker delivery) })) world
    have first := sent.bind (next := fun _ => pure (ForInStep.yield PUnit.unit)) (.pure _ _)
    have continued := ih { world with network := world.network.push (.worker delivery) }
    have network : world.network.push (.worker delivery) ++ rest.toArray.map Envelope.worker =
        world.network ++ (delivery :: rest).toArray.map Envelope.worker := by
      rw [Array.push_eq_append, List.toArray_cons delivery rest, Array.map_append, Array.map_singleton, Array.append_assoc]
    rw [show (delivery :: rest).toArray.size = (1 + 0) + rest.toArray.size by simp; omega]
    apply Execution.bind first
    simpa only [network] using! continued

/-- The mailbox receive has selected this delivery. One complete scheduler
turn performs exactly the declared state transition, publishes all replies,
and acknowledges that same receipt. Save, send, and acknowledgement are separate
atomic operations, so crash analysis can still stop at any boundary. -/
theorem turn_execution (generation duration : Nat) (world : World)
    (delivery : Received SchedulerMessage) (inbox : MailboxModel.Inbox SchedulerMessage)
    (received : MailboxModel.receive generation world.schedulerInbox = (some delivery, inbox)) :
    let handled := Scheduler.handle duration world.scheduler delivery.message
    Execution (Scheduler.turn (schedulerPorts generation) duration) world ()
      { world with scheduler := handled.1, network := world.network ++ handled.2.map Envelope.worker, schedulerInbox := MailboxModel.acknowledge generation delivery.receipt inbox }
      (4 + handled.2.size) := by
  dsimp only
  unfold Scheduler.turn
  have reserve := Execution.send true "scheduler.receive" (fun world : World =>
    let (delivery, inbox) := MailboxModel.receive generation world.schedulerInbox
    (delivery, { world with schedulerInbox := inbox })) world
  simp only [received] at reserve
  have loaded := Execution.send false "scheduler.load" (fun world : World => (world.scheduler, world))
    { world with schedulerInbox := inbox }
  let handled := Scheduler.handle duration world.scheduler delivery.message
  have saved := Execution.send false "scheduler.save" (fun world : World =>
    ((), { world with scheduler := handled.1 })) { world with schedulerInbox := inbox }
  have sent := send_all generation handled.2 { world with scheduler := handled.1, schedulerInbox := inbox }
  have acked := Execution.send true "scheduler.acknowledge" (fun world : World =>
    ((), { world with schedulerInbox := MailboxModel.acknowledge generation delivery.receipt world.schedulerInbox }))
    { world with scheduler := handled.1, schedulerInbox := inbox, network := world.network ++ handled.2.map Envelope.worker }
  rw [show 4 + handled.2.size = 1 + (1 + (1 + (handled.2.size + 1))) by omega]
  apply Execution.bind reserve
  apply Execution.bind loaded
  apply Execution.bind saved
  apply Execution.bind sent
  exact acked

/-- A delivered completion for a still-live attempt can become durable
scheduler progress in one uninterrupted turn. The actual outgoing acknowledgement
is confirmed before the incoming receipt is removed. A root completion finishes
the workflow. Expired attempts instead obey `stale_report_preserves_progress`. -/
theorem completion_can_be_saved (generation duration : Nat) (world : World)
    (report : Report) (receipt : Nat) (inbox : MailboxModel.Inbox SchedulerMessage)
    (received : MailboxModel.receive generation world.schedulerInbox =
      (some ⟨receipt, .report report⟩, inbox))
    (job : Scheduler.Job) (deadline : Nat)
    (valid : SchedulerAssignments.Valid world.scheduler) (member : job ∈ world.scheduler.jobs)
    (running : job.status = .running report.worker report.attempt deadline)
    (completed : report.progress = .ok .done) :
    let run : Simulation.Start World Unit 1 := fun _ _ => Scheduler.turn (schedulerPorts generation) duration
    ∃ events final,
      (∀ event ∈ events, event = .commit 0 ∨ event = .resume 0) ∧
      Simulation.run run events (Simulation.State.initial world run) = .ok final ∧
      final.actors 0 = .finished () ∧
      SchedulerProgress.Done final.world.scheduler.jobs job.branch ∧
      (job.branch = Location.root → final.world.scheduler.finished = true) ∧
      final.world.records = world.records ∧
      final.world.network = world.network.push (.worker ⟨report.worker, .acknowledged report.attempt⟩) ∧
      final.world.schedulerInbox = MailboxModel.acknowledge generation receipt inbox := by
  dsimp only
  let run : Simulation.Start World Unit 1 := fun _ _ => Scheduler.turn (schedulerPorts generation) duration
  let initial := Simulation.State.initial world run
  have executed := turn_execution generation duration world ⟨receipt, .report report⟩ inbox received
  obtain ⟨events, onlyActor, _, finished⟩ := executed.run run 0 initial rfl rfl
  have done := SchedulerProgress.completion_marks_done world.scheduler report job deadline valid member running completed
  refine ⟨events, _, onlyActor, finished, by simp [Simulation.State.setActor], done, ?_, rfl, ?_, rfl⟩
  · intro root
    obtain ⟨saved, present, branch, status⟩ := done
    exact Array.any_eq_true'.mpr ⟨saved, present, by simp [branch, root, status, Scheduler.done_iff]⟩
  · simp only [Scheduler.handle, Array.map_singleton, Array.push_eq_append]

/-- A live fork report can durably create its child jobs through the same
mailbox turn. If every child is already done, the saved parent is ready to join
instead of waiting for a report that will never arrive. -/
theorem fork_can_be_saved (generation duration : Nat) (world : World)
    (report : Report) (receipt : Nat) (inbox : MailboxModel.Inbox SchedulerMessage)
    (received : MailboxModel.receive generation world.schedulerInbox =
      (some ⟨receipt, .report report⟩, inbox))
    (job : Scheduler.Job) (deadline : Nat) (location : Location) (count : Nat)
    (valid : SchedulerAssignments.Valid world.scheduler) (member : job ∈ world.scheduler.jobs)
    (running : job.status = .running report.worker report.attempt deadline)
    (forked : report.progress = .ok (.fork location count)) :
    let run : Simulation.Start World Unit 1 := fun _ _ => Scheduler.turn (schedulerPorts generation) duration
    ∃ events final,
      (∀ event ∈ events, event = .commit 0 ∨ event = .resume 0) ∧
      Simulation.run run events (Simulation.State.initial world run) = .ok final ∧
      final.actors 0 = .finished () ∧
      (∃ updated ∈ final.world.scheduler.jobs,
        updated.branch = job.branch ∧ updated.location = location ∧
        (updated.status = .waiting ((Array.range count).map location.child) ∨
          updated.status = .pending ∧ updated.joining = true)) ∧
      (∀ index : Fin count, SchedulerProgress.Has final.world.scheduler.jobs (location.child index)) ∧
      final.world.records = world.records ∧
      final.world.network = world.network.push (.worker ⟨report.worker, .acknowledged report.attempt⟩) ∧
      final.world.schedulerInbox = MailboxModel.acknowledge generation receipt inbox := by
  dsimp only
  let run : Simulation.Start World Unit 1 := fun _ _ => Scheduler.turn (schedulerPorts generation) duration
  let initial := Simulation.State.initial world run
  have executed := turn_execution generation duration world ⟨receipt, .report report⟩ inbox received
  obtain ⟨events, onlyActor, _, finished⟩ := executed.run run 0 initial rfl rfl
  have scheduled := SchedulerProgress.fork_schedules_children world.scheduler report job deadline location count
    valid member running forked
  refine ⟨events, _, onlyActor, finished, by simp [Simulation.State.setActor], scheduled.1, scheduled.2,
    rfl, ?_, rfl⟩
  simp only [Scheduler.handle, Array.map_singleton, Array.push_eq_append]

end LeanCloud.Proofs.SchedulerDelivery
