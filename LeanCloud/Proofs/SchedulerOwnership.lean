import LeanCloud.SimulationBackend
import LeanCloud.Proofs.SimulationOwnership
import LeanCloud.Proofs.ActorEffects

/-! The scheduler database is a private field in Sim, just as it is private
storage in the container runtime. The same scheduler code runs in both. -/

namespace LeanCloud.Proofs.SchedulerOwnership
open SimulationBackend SimulationOwnership

abbrev Allowed (owner : Bool) {β : Type} : Atomic World β → Prop :=
  SimulationOwnership.Allowed World.scheduler owner
abbrev Program (owner : Bool) (program : SimM World α) := Effects.Program (Allowed owner) program

private theorem atomic (owner : Bool) (operation : World → α × World) (label : String)
    (preserves : ∀ world, (operation world).2.scheduler = world.scheduler) :
    Program owner (SimM.atomic operation label) := Effects.send _ (fun _ => preserves)

private theorem local_owner (operation : World → α × World) (label : String) :
    Program true (SimM.local operation label) := Effects.send _ (by simp [Allowed, SimulationOwnership.Allowed])

theorem receive (generation : Nat) : Program true (schedulerPorts generation).inbox.receive :=
  atomic true _ _ (fun _ => rfl)

theorem acknowledge (generation receipt : Nat) :
    Program true ((schedulerPorts generation).inbox.acknowledge receipt) := atomic true _ _ (fun _ => rfl)

theorem load (generation : Nat) : Program true (schedulerPorts generation).localDb.load := local_owner _ _

theorem save (generation : Nat) (state : Scheduler.State) :
    Program true ((schedulerPorts generation).localDb.save state) := local_owner _ _

theorem send (generation : Nat) (delivery : Delivery) :
    Program true ((schedulerPorts generation).send delivery) := atomic true _ _ (fun _ => rfl)

theorem worker_receive (worker : WorkerId) (generation : Nat) :
    Program false (workerPorts worker generation).inbox.receive := atomic false _ _ (fun _ => rfl)

theorem worker_acknowledge (worker : WorkerId) (generation receipt : Nat) :
    Program false ((workerPorts worker generation).inbox.acknowledge receipt) := atomic false _ _ (fun _ => rfl)

theorem worker_send (worker : WorkerId) (generation : Nat) (message : SchedulerMessage) :
    Program false ((workerPorts worker generation).send message) := atomic false _ _ (fun _ => rfl)

theorem record_read (key : String) : Program false (records.read key) := atomic false _ _ (fun _ => rfl)

theorem record_create (key : String) (record : ReplayRecord) : Program false (records.create key record) := by
  apply atomic
  intro world
  cases found : world.records.lookup key <;> simp [create, found]

theorem observed_read (worker : WorkerId) (key : String) : Program false ((observed worker).records.read key) := by
  apply Effects.bind _ (record_read key)
  intro result
  split
  · apply Effects.bind _ (Effects.send _ (fun _ _ => rfl))
    intro _
    trivial
  · trivial

theorem observed_create (worker : WorkerId) (key : String) (record : ReplayRecord) :
    Program false ((observed worker).records.create key record) := by
  apply Effects.bind _ (record_create key record)
  intro accepted
  apply Effects.bind _ (Effects.send _ (fun _ _ => rfl))
  intro _
  trivial

theorem confirmed (worker : WorkerId) : Program false (observed worker).confirmed :=
  Effects.send _ (fun _ _ => rfl)

/-- Actor bookkeeping preserves the supplied interpreter contract. The shared
actor proof covers the real turns, loops, startup, and recovery. -/
theorem start_programs [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι)
    (execution : ∀ worker assignment,
      Program false ((ReplayInterpreter.step (observed worker).records blobs fuel program input assignment).run)) :
    ∀ actor generation,
      Program (actor == (⟨0, Nat.zero_lt_succ workers⟩ : Fin (workers + 1)))
        (start (workers := workers) turns fuel duration program input actor generation) := by
  apply ActorEffects.start_programs
    (fun actor => Allowed (actor == (⟨0, Nat.zero_lt_succ workers⟩ : Fin (workers + 1))))
    turns fuel duration program input
  · intro generation
    simp only [beq_self_eq_true]
    exact ⟨receive generation, acknowledge generation, load generation, save generation, send generation⟩
  · intro actor other generation
    have different : (actor == (⟨0, Nat.zero_lt_succ workers⟩ : Fin (workers + 1))) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, Fin.ext_iff]
      exact other
    rw [different]
    exact ⟨worker_receive _ generation, worker_acknowledge _ generation, worker_send _ generation,
      confirmed _, execution _⟩
  · intro actor generation
    split <;> exact fun _ _ => rfl

/-- A delayed network event never accesses the scheduler's private database. -/
theorem network (event : NetworkEvent) (world : World) :
    (networkStep event world).scheduler = world.scheduler := by
  cases event <;> simp only [networkStep]
  all_goals repeat first | split | rfl

theorem disconnect (actor generation : Nat) (world : World) :
    (SimulationBackend.disconnect actor generation world).scheduler = world.scheduler := by
  simp only [SimulationBackend.disconnect]
  split <;> rfl

/-- This is the actual backend event, including the broker's crash hook. The
only event that may write coordination state is a commit by its owner. The
program premise describes allowed requests and all suspended continuations;
it does not assume the conclusion about execution traces. -/
theorem step_preserves (owner : Fin count) (start : Simulation.Start World α count)
    (starts : ∀ actor generation, Program (actor == owner) (start actor generation))
    (state after : Simulation.State World α count) (event : Simulation.Event count)
    (valid : SimulationOwnership.Valid World.scheduler owner state)
    (executed : SimulationBackend.step start event state = .ok after) :
    SimulationOwnership.Valid World.scheduler owner after ∧
      (event = .commit owner ∨ after.world.scheduler = state.world.scheduler) := by
  unfold SimulationBackend.step at executed
  cases result : Simulation.step start event state with
  | error error =>
    rw [result] at executed
    change Except.error error = Except.ok after at executed
    cases executed
  | ok next =>
    have safe := SimulationOwnership.step_preserves World.scheduler owner start starts state next event valid result
    rw [result] at executed
    cases event <;> change Except.ok _ = Except.ok after at executed <;> cases executed
    all_goals first
    | exact safe
    | exact ⟨⟨safe.1.actors, safe.1.orphans⟩, .inr ((disconnect _ _ _).trans (by simpa using safe.2))⟩

/-- Finite executions of existing backend events. The event predicate can
describe all executions or an interval while a particular actor is paused. -/
inductive Trace (start : Simulation.Start World α count) (allowed : Simulation.Event count → Prop) :
    Simulation.State World α count → Simulation.State World α count → Prop where
  | refl (state) : Trace start allowed state state
  | actor {before middle after} (history : Trace start allowed before middle)
      (event : Simulation.Event count) (admissible : allowed event)
      (executed : SimulationBackend.step start event middle = .ok after) :
      Trace start allowed before after
  | network {before middle} (history : Trace start allowed before middle) (event : NetworkEvent) :
      Trace start allowed before { middle with world := networkStep event middle.world }

theorem Trace.trans {start : Simulation.Start World α count} {allowed} {before middle after}
    (first : Trace start allowed before middle) (last : Trace start allowed middle after) :
    Trace start allowed before after := by
  induction last with
  | refl => exact first
  | actor _ event admissible executed ih => exact .actor ih event admissible executed
  | network _ event ih => exact .network ih event

abbrev Interference (owner : Fin count) (start : Simulation.Start World α count) :=
  Trace start (fun event => event ≠ .commit owner)

theorem trace_preserves (owner : Fin count) (start : Simulation.Start World α count)
    (starts : ∀ actor generation, Program (actor == owner) (start actor generation))
    {allowed : Simulation.Event count → Prop} {before after : Simulation.State World α count}
    (valid : SimulationOwnership.Valid World.scheduler owner before)
    (history : Trace start allowed before after) :
    SimulationOwnership.Valid World.scheduler owner after := by
  induction history with
  | refl => exact valid
  | actor history event admissible executed ih =>
    exact (step_preserves owner start starts _ _ event ih executed).1
  | network history event ih => exact ⟨ih.actors, ih.orphans⟩

/-- Other actors and durable transport cannot invalidate a scheduler's loaded
database snapshot. This also includes orphan requests from crashed actors. A
scheduler restart discards the old continuation; its next save is a new owner
commit, outside this interval. -/
theorem interference_preserves (owner : Fin count) (start : Simulation.Start World α count)
    (starts : ∀ actor generation, Program (actor == owner) (start actor generation))
    {before after : Simulation.State World α count}
    (valid : SimulationOwnership.Valid World.scheduler owner before)
    (history : Interference owner start before after) :
    SimulationOwnership.Valid World.scheduler owner after ∧ after.world.scheduler = before.world.scheduler := by
  induction history with
  | refl => exact ⟨valid, rfl⟩
  | actor history event paused executed ih =>
    have safe := step_preserves owner start starts _ _ event ih.1 executed
    exact ⟨safe.1, (safe.2.resolve_left paused).trans ih.2⟩
  | network history event ih =>
    exact ⟨⟨ih.1.actors, ih.1.orphans⟩, (network event _).trans ih.2⟩

end LeanCloud.Proofs.SchedulerOwnership
