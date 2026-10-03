import LeanCloud.SimulationBackend
import LeanCloud.Proofs.Effects

/-! Port contracts lift through the existing actor code. Ownership and replay
record preservation share these structural checks, including every restart. -/

namespace LeanCloud.Proofs.ActorEffects
open LeanEff SimulationBackend

universe u
variable {e : Type → Type u} {allowed : {β : Type} → e β → Prop}

structure SchedulerContract (allowed : {β : Type} → e β → Prop)
    (ports : SchedulerPorts (EffF e)) : Prop where
  receive : Effects.Program allowed ports.inbox.receive
  acknowledge : ∀ receipt, Effects.Program allowed (ports.inbox.acknowledge receipt)
  load : Effects.Program allowed ports.localDb.load
  save : ∀ state, Effects.Program allowed (ports.localDb.save state)
  send : ∀ delivery, Effects.Program allowed (ports.send delivery)

structure WorkerContract (allowed : {β : Type} → e β → Prop)
    (ports : Worker.Ports (EffF e)) (fuel : Nat)
    (program : ι → Cloud (EffF e) α) (input : ι) [Codec α] : Prop where
  receive : Effects.Program allowed ports.inbox.receive
  acknowledge : ∀ receipt, Effects.Program allowed (ports.inbox.acknowledge receipt)
  send : ∀ message, Effects.Program allowed (ports.send message)
  confirmed : Effects.Program allowed ports.observe.confirmed
  execution : ∀ assignment, Effects.Program allowed
    (ReplayInterpreter.step ports.observe.records ports.blobs fuel program input assignment).run

theorem recover {ports : SchedulerPorts (EffF e)} (valid : SchedulerContract allowed ports) :
    Effects.Program allowed (Scheduler.recover ports.localDb) :=
  Effects.bind _ valid.load (fun _ => valid.save _)

theorem scheduler_turn {ports : SchedulerPorts (EffF e)} (valid : SchedulerContract allowed ports)
    (duration : Nat) : Effects.Program allowed (Scheduler.turn ports duration) := by
  unfold Scheduler.turn
  apply Effects.bind _ valid.receive
  intro delivery
  cases delivery with
  | none => trivial
  | some delivery =>
    apply Effects.bind _ valid.load
    intro state
    apply Effects.bind _ (valid.save _)
    intro _
    apply Effects.bind
    · apply Effects.forIn_array
      intro message state
      apply Effects.bind _ (valid.send message)
      intro _
      trivial
    · intro _
      exact valid.acknowledge delivery.receipt

theorem worker_execute [Codec α] {ports : Worker.Ports (EffF e)}
    {fuel : Nat} {program : ι → Cloud (EffF e) α} {input : ι}
    (valid : WorkerContract allowed ports fuel program input) (assignment : Assignment) :
    Effects.Program allowed (Worker.execute ports.id ports.observe ports.blobs fuel program input assignment) :=
  Effects.bind _ (valid.execution assignment) (fun _ =>
    Effects.bind _ valid.confirmed (fun _ => trivial))

theorem worker_turn [Codec α] {ports : Worker.Ports (EffF e)}
    {fuel : Nat} {program : ι → Cloud (EffF e) α} {input : ι}
    (valid : WorkerContract allowed ports fuel program input) (state : Worker.State) :
    Effects.Program allowed (Worker.turn ports fuel program input state) := by
  unfold Worker.turn
  split
  · trivial
  · apply Effects.bind _ valid.receive
    intro delivery
    cases delivery with
    | none =>
      dsimp only
      split
      · apply Effects.bind _ (valid.send _)
        intro _
        trivial
      · trivial
    | some delivery =>
      rcases delivery with ⟨receipt, message⟩
      dsimp only
      cases message <;> dsimp only
      all_goals repeat first
        | exact Effects.pure _ _
        | apply Effects.bind _ (worker_execute valid _)
        | apply Effects.bind _ (valid.send _)
        | apply Effects.bind _ (valid.acknowledge _)
        | intro _
        | split

theorem scheduler_loop {allowed : {β : Type} → Atomic World β → Prop}
    (turns duration generation : Nat) (valid : SchedulerContract allowed (schedulerPorts generation)) :
    Effects.Program allowed (schedulerLoop turns duration generation) := by
  induction turns with
  | zero => trivial
  | succ turns ih => exact Effects.bind _ (scheduler_turn valid duration) (fun _ => ih)

theorem worker_loop [Codec α] {allowed : {β : Type} → Atomic World β → Prop}
    (turns fuel : Nat) (ports : Worker.Ports (SimM World)) (program : ι → Cloud (SimM World) α)
    (input : ι) (state : Worker.State) (valid : WorkerContract allowed ports fuel program input) :
    Effects.Program allowed (workerLoop turns fuel ports program input state) := by
  induction turns generalizing state with
  | zero => trivial
  | succ turns ih =>
    apply Effects.bind _ (worker_turn valid state)
    intro next
    split
    · exact ih next
    · trivial

/-- Actual Sim startup, including the consumer connection, private DB recovery,
and the actor loop. The allowed request property may depend on actor identity. -/
theorem start_programs [Codec α]
    (allowed : Fin (workers + 1) → {β : Type} → Atomic World β → Prop)
    (turns fuel duration : Nat) (program : ι → Cloud (SimM World) α) (input : ι)
    (scheduler : ∀ generation, SchedulerContract (allowed ⟨0, Nat.zero_lt_succ workers⟩) (schedulerPorts generation))
    (worker : ∀ actor : Fin (workers + 1), actor.val ≠ 0 → ∀ generation,
      WorkerContract (allowed actor) (workerPorts s!"worker-{actor.val}" generation) fuel program input)
    (connect : ∀ actor generation,
      if actor.val == 0 then
        allowed actor (.step true "scheduler.connect" (fun world => ((), { world with
          schedulerInbox := MailboxModel.connect generation world.schedulerInbox })))
      else
        allowed actor (.step true "worker.connect" (fun world =>
          let id := s!"worker-{actor.val}"
          let inbox := MailboxModel.connect generation ((world.workerInboxes.lookup id).getD {})
          ((), { world with workerInboxes := (id, inbox) :: world.workerInboxes.filter (fun entry => entry.1 != id) })))) :
    ∀ actor generation, Effects.Program (allowed actor)
      (start turns fuel duration program input actor generation) := by
  intro actor generation
  have connected := connect actor generation
  by_cases zero : actor.val = 0
  · have same : actor = ⟨0, Nat.zero_lt_succ workers⟩ := Fin.ext zero
    subst actor
    simp only [beq_self_eq_true, ite_true] at connected
    unfold start
    simp only [beq_self_eq_true, ite_true]
    apply Effects.bind _ (Effects.send _ connected)
    intro _
    exact Effects.bind _ (recover (scheduler generation)) (fun _ => scheduler_loop turns duration generation (scheduler generation))
  · simp only [beq_iff_eq, zero, ite_false] at connected
    unfold start
    simp only [beq_iff_eq, zero, ite_false]
    apply Effects.bind _ (Effects.send _ connected)
    intro _
    exact worker_loop turns fuel _ program input {} (worker actor zero generation)

end LeanCloud.Proofs.ActorEffects
