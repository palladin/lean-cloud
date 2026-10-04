import LeanCloud.Proofs.RecordPreservation
import LeanCloud.Proofs.InterpreterEffects
import LeanCloud.Proofs.SchedulerOwnership
import LeanCloud.Proofs.SimulationEvolution

/-! Committed replay records survive actual concurrent executions. This checks
the deployed actor/interpreter code through Sim's ports, including delayed
replies, restarts, and orphan requests; it does not assume record preservation
as a trace invariant. -/

namespace LeanCloud.Proofs.ReplayEvolution
open Lean LeanEff SimulationBackend ReplayModel

def Advances (before after : World) : Prop := Extends before.records after.records
abbrev Allowed {β : Type} : Atomic World β → Prop := SimulationEvolution.Allowed Advances
abbrev Program (program : SimM World α) := Effects.Program Allowed program
abbrev Valid (state : Simulation.State World α count) :=
  SimulationEvolution.Valid (fun _ => Allowed) Advances state
abbrev CloudProgram (program : Cloud (SimM World) α) := CloudEffects.Program (fun action => Program action) program

private theorem unchanged (remote : Bool) (label : String) (operation : World → α × World)
    (preserves : ∀ world, (operation world).2.records = world.records) :
    Program (EffF.send (.step remote label operation)) := by
  apply Effects.send
  intro world
  change Extends world.records (operation world).2.records
  rw [preserves world]
  exact Extends.refl _

private theorem read (key : String) : Program (records.read key) := unchanged _ _ _ (fun _ => rfl)

private theorem create (key : String) (record : ReplayRecord) : Program (records.create key record) :=
  Effects.send _ (fun world => simulated_create_extends world key record)

private theorem observed_read (worker : WorkerId) (key : String) : Program ((observed worker).records.read key) := by
  apply Effects.bind _ (read key)
  intro result
  split
  · apply Effects.bind _ (unchanged _ _ _ (fun _ => rfl))
    intro _
    trivial
  · trivial

private theorem observed_create (worker : WorkerId) (key : String) (record : ReplayRecord) :
    Program ((observed worker).records.create key record) := by
  apply Effects.bind _ (create key record)
  intro accepted
  apply Effects.bind _ (unchanged _ _ _ (fun _ => rfl))
  intro _
  trivial

private theorem execute (codec : Codec α) (operation : Operation (SimM World) α)
    (valid : CloudEffects.Request (fun action => Program action) (.command codec operation)) :
    Program (blobs.execute operation).run := by
  cases operation with
  | exec label body => exact Effects.except_lift _ valid
  | putBlob bytes =>
    dsimp only [BlobStorage.execute, blobs]
    exact Effects.except_lift _ (unchanged _ _ _ (fun _ => rfl))
  | readBlob ref =>
    apply Effects.except_bind _ (Effects.except_lift _ (unchanged _ _ _ (fun _ => rfl)))
    intro bytes
    cases bytes with
    | none => trivial
    | some bytes => dsimp only; split <;> trivial
  | resolveBlob name =>
    apply Effects.except_bind _ (Effects.except_lift _ (unchanged _ _ _ (fun _ => rfl)))
    intro ref
    cases ref <;> trivial

private theorem interpreter_ports (worker : WorkerId) :
    InterpreterEffects.Ports Allowed (observed worker).records blobs :=
  ⟨observed_read worker, observed_create worker, execute⟩

/-- All actual actor requests preserve existing records. Only `exec` bodies
require a source contract; record creation, blobs, coordination and mail are
checked here. The condition permits new records but forbids replacing old ones. -/
theorem start_programs [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (valid : CloudProgram (program input)) :
    ∀ actor generation, Program (start (workers := workers) turns fuel duration program input actor generation) := by
  apply ActorEffects.start_programs (fun _ => Allowed) turns fuel duration program input
  · intro generation
    refine ⟨unchanged _ _ _ (fun _ => rfl), ?_, unchanged _ _ _ (fun _ => rfl), ?_, ?_⟩
    all_goals intro _; exact unchanged _ _ _ (fun _ => rfl)
  · intro actor other generation
    refine ⟨unchanged _ _ _ (fun _ => rfl), ?_, ?_, unchanged _ _ _ (fun _ => rfl), ?_⟩
    · intro _; exact unchanged _ _ _ (fun _ => rfl)
    · intro _; exact unchanged _ _ _ (fun _ => rfl)
    · intro assignment
      exact InterpreterEffects.step_preserves (interpreter_ports _) fuel program input assignment valid
  · intro actor generation
    split <;> exact fun world => Extends.refl world.records

theorem network (event : NetworkEvent) (world : World) : (networkStep event world).records = world.records := by
  cases event <;> simp only [networkStep]
  all_goals repeat first | split | rfl

theorem disconnect (actor generation : Nat) (world : World) :
    (SimulationBackend.disconnect actor generation world).records = world.records := by
  unfold SimulationBackend.disconnect
  split <;> rfl

theorem step_preserves (start : Simulation.Start World α count)
    (starts : ∀ actor generation, Program (start actor generation))
    (state after : Simulation.State World α count) (event : Simulation.Event count)
    (valid : Valid state)
    (executed : SimulationBackend.step start event state = .ok after) :
    Valid after ∧ Advances state.world after.world := by
  unfold SimulationBackend.step at executed
  cases result : Simulation.step start event state with
  | error error =>
    rw [result] at executed
    change Except.error error = Except.ok after at executed
    cases executed
  | ok next =>
    have eventSafe := SimulationEvolution.step_preserves (fun _ => Advances)
      (orphanAdvance := Advances) (fun world => Extends.refl world.records) start starts
      (by intro actor β remote label operation sound; exact sound)
      (by intro actor β label operation sound; exact sound)
      state next event valid result
    have grows : Advances state.world next.world := by
      rcases eventSafe.2 with ⟨_, _, grows⟩ | grows <;> exact grows
    have safe : Valid next ∧ Advances state.world next.world := ⟨eventSafe.1, grows⟩
    rw [result] at executed
    cases event <;> change Except.ok _ = Except.ok after at executed <;> cases executed
    all_goals first
    | exact safe
    | exact ⟨⟨safe.1.actors, safe.1.orphans⟩, by
        change Extends state.world.records (SimulationBackend.disconnect _ _ next.world).records
        rw [disconnect]
        exact safe.2⟩

/-- Record growth across any finite interleaving, including both actor events
and durable transport. No fairness or crash-free interval is needed for safety. -/
theorem trace_preserves (start : Simulation.Start World α count)
    (starts : ∀ actor generation, Program (start actor generation))
    {allowed : Simulation.Event count → Prop} {before after : Simulation.State World α count}
    (valid : Valid before)
    (history : SchedulerOwnership.Trace start allowed before after) :
    Valid after ∧ Extends before.world.records after.world.records := by
  induction history with
  | refl => exact ⟨valid, Extends.refl _⟩
  | actor history event admissible executed ih =>
    have safe := step_preserves start starts _ _ event ih.1 executed
    exact ⟨safe.1, ih.2.trans safe.2⟩
  | network history event ih =>
    exact ⟨⟨ih.1.actors, ih.1.orphans⟩, by rw [network]; exact ih.2⟩

/-- The preservation premise of `trace_preserves` follows from actual startup
and the source action contract, for all generations of every actor. -/
theorem reachable [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (valid : CloudProgram (program input)) (world : World)
    {after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial world (start turns fuel duration program input)) after) :
    Valid after :=
  (trace_preserves _ (start_programs workers turns fuel duration program input valid)
    (SimulationEvolution.initial (orphanAdvance := Advances) world _ (start_programs workers turns fuel duration program input valid)) history).1

/-- A record obtained at a reachable state is still there after arbitrary
interference, even if the reader has not yet received its reply or has crashed. -/
theorem record_survives [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (valid : CloudProgram (program input)) (world : World)
    {before after : Simulation.State World Unit (workers + 1)}
    (past : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial world (start turns fuel duration program input)) before)
    (future : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True) before after)
    (key : String) (record : ReplayRecord) (present : before.world.records.lookup key = some record) :
    after.world.records.lookup key = some record :=
  (trace_preserves _ (start_programs workers turns fuel duration program input valid)
    (reachable workers turns fuel duration program input valid world past) future).2 key record present

/-- The actual store's commit saves the canonical winner before replying. That
same value remains visible after any later interleaving, whether or not this
worker receives the reply, resumes, or survives. -/
theorem creation_reply_survives [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (valid : CloudProgram (program input)) (world : World)
    {before committed after : Simulation.State World Unit (workers + 1)}
    (past : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial world (start turns fuel duration program input)) before)
    (actor : Fin (workers + 1)) (key : String) (proposed : ReplayRecord)
    (next : ArrsF (Atomic World) Empty ReplayRecord Unit)
    (waiting : before.actors actor = .waiting true s!"record.create:{key}" (SimulationBackend.create key proposed) next)
    (executed : SimulationBackend.step (start turns fuel duration program input) (.commit actor) before = .ok committed)
    (future : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True) committed after) :
    let accepted := (SimulationBackend.create key proposed before.world).1
    committed.actors actor = .responding accepted next ∧
      after.world.records.lookup key = some accepted := by
  have extended := past.actor (.commit actor) trivial executed
  have actual := executed
  simp only [SimulationBackend.step, Simulation.step, waiting] at actual
  cases actual
  refine ⟨by simp [Simulation.State.setActor], ?_⟩
  exact record_survives workers turns fuel duration program input valid world extended future key _
    (create_is_visible before.world key proposed)

end LeanCloud.Proofs.ReplayEvolution
