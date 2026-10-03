import LeanCloud.Proofs.ConcurrentSafety
import LeanCloud.Proofs.PureDirect
import LeanCloud.Proofs.WorkerOwnership
import LeanCloud.Proofs.WorkerProgress
import LeanCloud.Proofs.SchedulerDelivery
import LeanCloud.Proofs.CoordinationProgress
import LeanCloud.Proofs.DeploymentProgress
import LeanCloud.Proofs.SequentialReplay

/-! Review entry point for interpreter equivalence.

`sequential_replay_matches_direct`: from empty storage, sequentially driving
the actual replay step returns the direct result with sufficient fuel. This
basic theorem needs no scheduler, mailbox, crash, or fairness assumptions.

`completed_replay_matches_direct`: whenever the scheduler finishes, the stored
root result equals direct evaluation. No fairness or fuel bound is required.

`concurrent_replay_matches_direct`: a pure workflow eventually finishes with that
same result, given sufficient interpreter fuel and recurring timely processing
windows. The source determines one fuel bound for all workers and assignments.
The environment must allow execution, delivery, and a save while the attempt is
live; it does not supply successful reports or the expected result.

Both concurrent theorems use the original program, the actual actor code, and traces from empty
storage. Durable delivery alone does not guarantee the processing windows:
endless crashes or expiry before every report can prevent completion.

`ConcurrentSafety.root_result` also proves any published root result correct
before scheduler completion. See `LeanCloud/Proofs/README.md`
for the precise environment assumptions and supporting proofs. -/

namespace LeanCloud.Proofs
open SimulationBackend

/-- A pure workflow has the same final result under direct evaluation and
sequential replay from empty storage, for every sufficiently large fuel budget.
Replay executes children, records their results, and reconstructs the parent
from the original source. Successes and application errors are both covered. -/
theorem sequential_replay_matches_direct [codec : Codec α]
    (program : ι → Cloud ReplayModel.M α) (input : ι)
    (pureProgram : ∃ outcome, Pure.Evaluation (program input) outcome)
    (roundtrip : Pure.RoundTrips codec) :
    ∃ sufficientFuel, ∀ fuel, sufficientFuel ≤ fuel →
      let direct := ((DirectInterpreter.interpret ReplayModel.noBlobs program input).run []).1
      let replay := ((LeanCloud.SequentialReplay.interpret ReplayModel.store ReplayModel.noBlobs fuel program input).run []).1
      replay = direct := by
  obtain ⟨outcome, evaluation⟩ := pureProgram
  obtain ⟨bound, replay⟩ := SequentialReplay.evaluates_from_empty ReplayModel.noBlobs (program input) evaluation roundtrip
  refine ⟨bound, fun fuel enough => ?_⟩
  have direct := congrFun (Pure.evaluation_matches_direct ReplayModel.noBlobs evaluation) []
  change (DirectInterpreter.interpret ReplayModel.noBlobs program input).run [] = (outcome, []) at direct
  dsimp only
  rw [direct]
  exact replay fuel enough

/-- If the scheduler finishes, global storage contains a root result and the
direct interpreter returns precisely that result for the same pure source and
input. This holds after arbitrary crashes, restarts, redelivery, and interleaving.
It does not assume correct records, reports, or intermediate scheduler states.
It does not claim that every execution eventually finishes. -/
theorem completed_replay_matches_direct [codec : Codec α]
    (workers turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι)
    (pureProgram : ∃ outcome, Pure.Evaluation (program input) outcome)
    (roundtrip : Pure.RoundTrips codec)
    (final : Simulation.State World Unit (workers + 1))
    (history : SchedulerOwnership.Trace (start turns fuel duration program input) (fun _ => True)
      (Simulation.State.initial {} (start turns fuel duration program input)) final)
    (finished : final.world.scheduler.finished = true) :
    let direct := (DirectInterpreter.interpret blobs program input).run
    let stored := final.world.records.lookup (ReplayStore.returnKey Location.root)
    match stored with
    | none => False
    | some record =>
        let replay := (ReplayInterpreter.result (m := Id) (α := α) record.outcome).run
        direct = LeanEff.EffF.pure replay := by
  obtain ⟨outcome, evaluation⟩ := pureProgram
  have durable := ConcurrentSafety.completed_result workers turns fuel duration program input evaluation history finished
  dsimp only
  rw [durable]
  change (DirectInterpreter.Internal.eval blobs (program input)).run = _
  rw [PureDirect.evaluation_matches_direct blobs evaluation, Worker.decode_recorded roundtrip]

/-- The concurrent replay deployment eventually stores precisely the direct
interpreter's result for the same pure program and input. The source supplies
a uniform sufficient fuel bound. The environment supplies recurring timely
processing windows (`DeploymentProgress.MakesProgress`), including delivery
and restart opportunities; it does not supply completion or correct results. -/
theorem concurrent_replay_matches_direct [codec : Codec α]
    (program : ι → Cloud (SimM World) α) (input : ι)
    (pureProgram : ∃ outcome, Pure.Evaluation (program input) outcome)
    (roundtrip : Pure.RoundTrips codec) :
    ∃ sufficientFuel, ∀ workers turns fuel duration, sufficientFuel ≤ fuel →
      ∀ run : DeploymentProgress.Run (start (workers := workers) turns fuel duration program input),
      DeploymentProgress.MakesProgress workers turns fuel duration program input run →
      ∃ index,
        let final := run.state index
        final.world.scheduler.finished = true ∧
        let direct := (DirectInterpreter.interpret blobs program input).run
        let stored := final.world.records.lookup (ReplayStore.returnKey Location.root)
        match stored with
        | none => False
        | some record =>
            let replay := (ReplayInterpreter.result (m := Id) (α := α) record.outcome).run
            direct = LeanEff.EffF.pure replay := by
  obtain ⟨outcome, evaluation⟩ := pureProgram
  obtain ⟨sufficientFuel, finishes⟩ := DeploymentProgress.eventually_finishes program input evaluation
  refine ⟨sufficientFuel, ?_⟩
  intro workers turns fuel duration enough run progress
  obtain ⟨index, finished⟩ := finishes workers turns fuel duration enough run progress
  exact ⟨index, finished, completed_replay_matches_direct workers turns fuel duration program input
    ⟨outcome, evaluation⟩ roundtrip (run.state index) (run.reachable index) finished⟩

end LeanCloud.Proofs
