import LeanCloud.Proofs.InterpreterEffects
import LeanCloud.Proofs.SchedulerOwnership

/-! The replay interpreter cannot write the scheduler database. The only
user-supplied base-monad actions are `exec` bodies; their ownership property is
lifted through Cloud syntax, decoding, replay, forks, joins, and failures. -/

namespace LeanCloud.Proofs.WorkerOwnership
open Lean LeanEff SimulationBackend ReplayInterpreter Internal

abbrev Protected (program : SimM World α) := SchedulerOwnership.Program false program
abbrev CloudProgram (program : Cloud (SimM World) α) := CloudEffects.Program (fun action => Protected action) program

private theorem execute (codec : Codec α) (operation : Operation (SimM World) α)
    (valid : CloudEffects.Request (fun action => Protected action) (.command codec operation)) :
    Protected (blobs.execute operation).run := by
  cases operation with
  | exec label body => exact Effects.except_lift _ valid
  | putBlob bytes =>
    dsimp only [BlobStorage.execute, blobs]
    exact Effects.except_lift _ (Effects.send _ (fun _ _ => rfl))
  | readBlob ref =>
    apply Effects.except_bind _ (Effects.except_lift _ (Effects.send _ (fun _ _ => rfl)))
    intro bytes
    cases bytes with
    | none => trivial
    | some bytes => dsimp only; split <;> trivial
  | resolveBlob name =>
    apply Effects.except_bind _ (Effects.except_lift _ (Effects.send _ (fun _ _ => rfl)))
    intro ref
    cases ref <;> trivial

private theorem ports (worker : WorkerId) :
    InterpreterEffects.Ports (SchedulerOwnership.Allowed false) (observed worker).records blobs :=
  ⟨SchedulerOwnership.observed_read worker, SchedulerOwnership.observed_create worker, execute⟩

theorem step_preserves [Codec α] (worker : WorkerId) (fuel : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (assignment : Assignment)
    (valid : CloudProgram (program input)) :
    Protected (ReplayInterpreter.step (observed worker).records blobs fuel program input assignment).run :=
  InterpreterEffects.step_preserves (ports worker) fuel program input assignment valid

/-- All actual actor starts, including restarts, respect private database
ownership once the user's actions do. There is no assumed interpreter contract. -/
theorem actors_preserve_ownership [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (valid : CloudProgram (program input)) :
    ∀ actor generation,
      SchedulerOwnership.Program (actor == (⟨0, Nat.zero_lt_succ workers⟩ : Fin (workers + 1)))
        (start (workers := workers) turns fuel duration program input actor generation) :=
  SchedulerOwnership.start_programs workers turns fuel duration program input
    (fun worker assignment => step_preserves worker fuel program input assignment valid)

theorem initial [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (valid : CloudProgram (program input)) (world : World) :
    SimulationOwnership.Valid World.scheduler ⟨0, Nat.zero_lt_succ workers⟩
      (Simulation.State.initial world (start (workers := workers) turns fuel duration program input)) :=
  SimulationOwnership.initial _ _ _ _ (actors_preserve_ownership workers turns fuel duration program input valid)

/-- During interference between scheduler operations, its durable state stays
unchanged. Workers use the actual interpreter and ports; messages and orphan
requests use the actual backend transitions. -/
theorem private_db_between_saves [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (valid : CloudProgram (program input))
    {before after : Simulation.State World Unit (workers + 1)}
    (owned : SimulationOwnership.Valid World.scheduler ⟨0, Nat.zero_lt_succ workers⟩ before)
    (history : SchedulerOwnership.Interference ⟨0, Nat.zero_lt_succ workers⟩
      (start turns fuel duration program input) before after) :
    after.world.scheduler = before.world.scheduler :=
  (SchedulerOwnership.interference_preserves _ _
    (actors_preserve_ownership workers turns fuel duration program input valid) owned history).2

/-- From actual startup, every reachable actor and orphan retains ownership.
No invariant about suspended workers or their interpreter is assumed here. -/
theorem reachable_ownership [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (valid : CloudProgram (program input)) (world : World)
    {after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial world (start turns fuel duration program input)) after) :
    SimulationOwnership.Valid World.scheduler ⟨0, Nat.zero_lt_succ workers⟩ after :=
  SchedulerOwnership.trace_preserves _ _ (actors_preserve_ownership workers turns fuel duration program input valid)
    (initial workers turns fuel duration program input valid world) history

/-- Only the scheduler can change its database. This holds after arbitrary
actual actor/network events, including independent crashes and restarts. User
actions must respect the same private-state boundary as the deployed workers. -/
theorem only_scheduler_writes [Codec α] (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) (valid : CloudProgram (program input)) (world : World)
    {before after : Simulation.State World Unit (workers + 1)}
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial world (start turns fuel duration program input)) before)
    (event : Simulation.Event (workers + 1)) (other : event ≠ .commit ⟨0, Nat.zero_lt_succ workers⟩)
    (executed : SimulationBackend.step (start turns fuel duration program input) event before = .ok after) :
    after.world.scheduler = before.world.scheduler :=
  (SchedulerOwnership.step_preserves _ _ (actors_preserve_ownership workers turns fuel duration program input valid)
    _ _ event (reachable_ownership workers turns fuel duration program input valid world history) executed).2.resolve_left other

end LeanCloud.Proofs.WorkerOwnership
