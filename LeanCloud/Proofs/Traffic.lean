import LeanCloud.SimulationBackend
import LeanCloud.Proofs.Mailbox
import LeanCloud.Proofs.SchedulerGroups
import LeanCloud.Proofs.SchedulerPaths

/-! Message validity survives durable transport. These predicates certify the
existing messages; they add no fields to envelopes, mailboxes, or runtime state. -/

namespace LeanCloud.Proofs.Traffic
open Lean ReplayModel SchedulerAssignments SchedulerRecords SimulationBackend

variable {m : Type → Type u} {α : Type}

/-- A live fork report advances its job's location; a completed child group
cannot cause the same suspension again. Expired attempts impose no constraint on a
replacement job, and their reports cannot change that job. -/
def ForkForward (state : Scheduler.State) (report : Report) : Prop :=
  ∀ job ∈ state.jobs, ∀ deadline location count,
    job.status = .running report.worker report.attempt deadline →
    report.progress = .ok (.fork location count) →
    Routing.Follows job.location location ∧ (job.joining = true → location ≠ job.location)

theorem ForkForward.advance {before after report} (valid : ForkForward before report)
    (old : report.attempt < before.nextAttempt) (forward : Forward before after) : ForkForward after report :=
  fun job member deadline location count running forked =>
    valid job (forward.2 job member report.worker report.attempt deadline running old)
      deadline location count running forked

def ToScheduler (encode : α → Json) (program : Cloud m α)
    (expected : Journal) (state : Scheduler.State) (journal : Journal) : SchedulerMessage → Prop
  | .report report => report.attempt < state.nextAttempt ∧ ReportBacked journal state report ∧ ForkBacked expected state report ∧
      Suspension.ReportPaths journal encode program report ∧ ForkForward state report
  | _ => True

def ToWorker (encode : α → Json) (program : Cloud m α)
    (expected : Journal) (state : Scheduler.State) (journal : Journal) (worker : WorkerId) : WorkerMessage → Prop
  | .execute issued => ∃ point : Checkpoint, point.work = issued ∧
      Identifies state worker point ∧ SchedulerGroups.AssignmentReady expected journal point ∧
      Reconstruction.Resumable journal encode program Location.root point.location
  | _ => True

def EnvelopeValid (encode : α → Json) (program : Cloud m α)
    (expected : Journal) (state : Scheduler.State) (journal : Journal) : Envelope → Prop
  | .scheduler message => ToScheduler encode program expected state journal message
  | .worker delivery => ToWorker encode program expected state journal delivery.worker delivery.message

variable {encode : α → Json} {program : Cloud m α}

theorem ToScheduler.advance {before after first last message} (valid : ToScheduler encode program expected before first message)
    (forward : Forward before after) (extension : Extends first last) : ToScheduler encode program expected after last message := by
  cases message with
  | report report =>
    exact ⟨Nat.lt_of_lt_of_le valid.1 forward.1, (valid.2.1.advance valid.1 forward).extend extension,
      valid.2.2.1.advance valid.1 forward, valid.2.2.2.1.extend extension,
      valid.2.2.2.2.advance valid.1 forward⟩
  | ready _ | tick _ | inspect _ => trivial

theorem ToWorker.advance {before after first last worker message} (valid : ToWorker encode program expected before first worker message)
    (forward : Forward before after) (extension : Extends first last) : ToWorker encode program expected after last worker message := by
  cases message with
  | execute issued =>
    obtain ⟨point, same, identity, ready, path⟩ := valid
    exact ⟨point, same, identity.advance forward, ready.extend extension, path.extend extension⟩
  | acknowledged _ | idle | finished | failed _ | status _ => trivial

theorem EnvelopeValid.advance {before after first last envelope} (valid : EnvelopeValid encode program expected before first envelope)
    (forward : Forward before after) (extension : Extends first last) : EnvelopeValid encode program expected after last envelope := by
  cases envelope with
  | scheduler message => exact ToScheduler.advance valid forward extension
  | worker delivery => exact ToWorker.advance valid forward extension

/-- Each emitted assignment has a proof checkpoint certifying its identity,
child readiness, and reconstruction path. Only the branch start and attempt
travel in the message, which can remain in transport through later restarts. -/
theorem scheduler_sends_valid (state : Scheduler.State) (expected journal : Journal) (duration : Nat) (message : SchedulerMessage)
    (valid : SchedulerAssignments.Valid state) (groups : SchedulerGroups.Valid expected journal state.jobs)
    (paths : SchedulerPaths.Valid journal encode program state.jobs) (delivery : Delivery)
    (sent : delivery ∈ (Scheduler.handle duration state message).2) :
    ToWorker encode program expected (Scheduler.handle duration state message).1 journal delivery.worker delivery.message := by
  cases kind : delivery.message with
  | execute issued =>
    obtain ⟨job, member, attempt, same, identity⟩ :=
      handle_identifies state duration message valid delivery issued sent kind
    exact ⟨Checkpoint.ofJob job attempt, same, identity,
      (groups job member).assignment attempt, paths job member⟩
  | acknowledged _ | idle | finished | failed _ | status _ => trivial

structure Valid (encode : α → Json) (program : Cloud m α) (expected : Journal) (world : World) : Prop where
  network : ∀ envelope ∈ world.network, EnvelopeValid encode program expected world.scheduler world.records envelope
  scheduler : Mailbox.All (ToScheduler encode program expected world.scheduler world.records) world.schedulerInbox
  workers : ∀ entry ∈ world.workerInboxes, Mailbox.All (ToWorker encode program expected world.scheduler world.records entry.1) entry.2

theorem initial (encode : α → Json) (program : Cloud m α) (expected : Journal) : Valid encode program expected {} := by
  constructor
  · simp
  · exact .empty _
  · simp

/-- Previously queued messages remain valid as the sole scheduler advances and
workers append immutable records. This includes messages from old attempts. -/
theorem Valid.advance {world : World} (valid : Valid encode program expected world) (state : Scheduler.State) (journal : Journal)
    (forward : Forward world.scheduler state) (extension : Extends world.records journal) :
    Valid encode program expected { world with scheduler := state, records := journal } := by
  constructor
  · exact fun envelope member => (valid.network envelope member).advance forward extension
  · exact valid.scheduler.mono (fun _ sound => sound.advance forward extension)
  · exact fun entry member => (valid.workers entry member).mono (fun _ sound => sound.advance forward extension)

theorem inbox_valid {world : World} (valid : Valid encode program expected world) (worker : WorkerId) :
    Mailbox.All (ToWorker encode program expected world.scheduler world.records worker) ((world.workerInboxes.lookup worker).getD {}) := by
  cases found : world.workerInboxes.lookup worker with
  | none => exact .empty _
  | some inbox =>
    obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp found
    exact valid.workers (worker, inbox) (by simp [entries])

theorem update_workers {world : World} (valid : Valid encode program expected world) (worker : WorkerId)
    (inbox : MailboxModel.Inbox WorkerMessage) (sound : Mailbox.All (ToWorker encode program expected world.scheduler world.records worker) inbox) :
    ∀ entry ∈ (worker, inbox) :: world.workerInboxes.filter (fun entry => entry.1 != worker),
      Mailbox.All (ToWorker encode program expected world.scheduler world.records entry.1) entry.2 := by
  intro entry member
  rcases List.mem_cons.mp member with same | previous
  · subst entry
    exact sound
  · exact valid.workers entry (List.mem_filter.mp previous).1

/-- A confirmed publication enters the same network used by the actual ports.
Its certificate can be advanced before a delayed or orphan publication commits. -/
theorem publish_preserves (world : World) (envelope : Envelope) (valid : Valid encode program expected world)
    (sound : EnvelopeValid encode program expected world.scheduler world.records envelope) :
    Valid encode program expected { world with network := world.network.push envelope } := by
  refine ⟨?_, valid.scheduler, valid.workers⟩
  intro value member
  rcases Array.mem_push.mp member with member | same
  · exact valid.network value member
  · subst value
    exact sound

private theorem erase_subset {items : Array α} {index : Nat} {item : α}
    (member : item ∈ items.eraseIdxIfInBounds index) : item ∈ items := by
  rw [Array.eraseIdxIfInBounds_eq] at member
  split at member
  · exact Array.mem_of_mem_eraseIdx member
  · exact member

/-- The actual simulation network preserves assignment identity and report
backing through delivery, duplication, arbitrary delay, and timer messages. -/
theorem network_preserves (world : World) (event : NetworkEvent) (valid : Valid encode program expected world) :
    Valid encode program expected (networkStep event world) := by
  cases event with
  | hold => exact valid
  | tick elapsed =>
    exact ⟨valid.network, valid.scheduler.publish (.tick elapsed) trivial, valid.workers⟩
  | duplicate index =>
    cases found : world.network[index]? with
    | none => simpa only [networkStep, found] using! valid
    | some envelope =>
      have sound := valid.network envelope (Array.mem_of_getElem? found)
      simpa only [networkStep, found] using! publish_preserves world envelope valid sound
  | deliver index =>
    cases found : world.network[index]? with
    | none => simpa only [networkStep, found] using! valid
    | some envelope =>
      have sound := valid.network envelope (Array.mem_of_getElem? found)
      have remaining : ∀ envelope ∈ world.network.eraseIdxIfInBounds index,
          EnvelopeValid encode program expected world.scheduler world.records envelope :=
        fun envelope member => valid.network envelope (erase_subset member)
      cases envelope with
      | scheduler message =>
        simp only [networkStep, found]
        exact ⟨remaining, valid.scheduler.publish message sound, valid.workers⟩
      | worker delivery =>
        simp only [networkStep, found]
        exact ⟨remaining, valid.scheduler,
          update_workers valid delivery.worker _ ((inbox_valid valid delivery.worker).publish delivery.message sound)⟩

/-- The broker's actual crash hook requeues in-flight messages without changing
their assignment identity or durable report backing. -/
theorem disconnect_preserves (world : World) (actor generation : Nat) (valid : Valid encode program expected world) :
    Valid encode program expected (SimulationBackend.disconnect actor generation world) := by
  unfold SimulationBackend.disconnect
  split
  · exact ⟨valid.network, valid.scheduler.disconnect generation, valid.workers⟩
  · exact ⟨valid.network, valid.scheduler,
      update_workers valid s!"worker-{actor}" _ ((inbox_valid valid _).disconnect generation)⟩

end LeanCloud.Proofs.Traffic
