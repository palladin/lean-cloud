import LeanCloud.Proofs.ReplayCompletion
import LeanCloud.Proofs.RecoveryCompletion

/-! The semantic review entry point: the same pure program and input have the
same result under direct evaluation, sequential replay, parallel replay, and
parallel replay with worker-local restarts. All replay drivers start with empty
storage and use `ReplayInterpreter.step`. Deployment policies remain runtime tests. -/

namespace LeanCloud.Proofs

/-- Sequential replay returns the direct result for every sufficiently large
fuel budget. Successes and application errors are both covered. -/
theorem sequential_replay_matches_direct [codec : Codec α]
    (program : ι → Cloud ReplayModel.M α) (input : ι)
    (pureProgram : ∃ outcome, Pure.Evaluation (program input) outcome)
    (roundtrip : Pure.RoundTrips codec) :
    ∃ sufficientFuel, ∀ fuel, sufficientFuel ≤ fuel →
      let direct := ((DirectInterpreter.interpret ReplayModel.noBlobs program input).run []).1
      let replay := ((SequentialReplay.interpret ReplayModel.store ReplayModel.noBlobs fuel program input).run []).1
      replay = direct := by
  obtain ⟨outcome, evaluation⟩ := pureProgram
  obtain ⟨bound, replay⟩ := ReplayCompletion.evaluates_from_empty (program input) .sequential evaluation roundtrip
  refine ⟨bound, fun fuel enough => ?_⟩
  have direct := congrFun (Pure.evaluation_matches_direct ReplayModel.noBlobs evaluation) []
  change (DirectInterpreter.interpret ReplayModel.noBlobs program input).run [] = (outcome, []) at direct
  dsimp only
  rw [direct]
  exact replay fuel enough

/-- Parallel replay returns the direct result for every sufficiently large
fuel budget. Children read the old journal and return disjoint new records.
Their union precedes parent resumption. Results retain source order. -/
theorem parallel_replay_matches_direct [codec : Codec α]
    (program : ι → Cloud ReplayModel.M α) (input : ι)
    (pureProgram : ∃ outcome, Pure.Evaluation (program input) outcome)
    (roundtrip : Pure.RoundTrips codec) :
    ∃ sufficientFuel, ∀ fuel, sufficientFuel ≤ fuel →
      let direct := ((DirectInterpreter.interpret ReplayModel.noBlobs program input).run []).1
      let replay := ((ParallelReplay.interpret fuel program input).run []).1
      replay = direct := by
  obtain ⟨outcome, evaluation⟩ := pureProgram
  obtain ⟨bound, replay⟩ := ReplayCompletion.evaluates_from_empty (program input) .parallel evaluation roundtrip
  refine ⟨bound, fun fuel enough => ?_⟩
  have direct := congrFun (Pure.evaluation_matches_direct ReplayModel.noBlobs evaluation) []
  change (DirectInterpreter.interpret ReplayModel.noBlobs program input).run [] = (outcome, []) at direct
  dsimp only
  rw [direct]
  exact replay fuel enough

/-- Parallel replay with local worker restarts returns the direct result for
every sufficiently large fuel budget and any finite worker fault plan. Direct
evaluation of the same pure program cannot raise a storage crash. -/
theorem restarting_parallel_replay_matches_direct [codec : Codec α]
    (program : ι → Cloud ReplayFaults.WorkerM α) (input : ι)
    (pureProgram : ∃ outcome, Pure.Evaluation (program input) outcome)
    (roundtrip : Pure.RoundTrips codec) (faults : ReplayFaults.Plan) :
    ∃ sufficientFuel, ∀ fuel, sufficientFuel ≤ fuel →
      let direct := ((DirectInterpreter.interpret ReplayFaults.noBlobs program input).run.run ⟨[], {}⟩).1
      let replay := ((RestartingParallelReplay.interpret fuel program input).run
        (ReplayFaults.Saved.initial faults)).1
      match direct with
      | .ok expected => replay = expected
      | .error _ => False := by
  obtain ⟨outcome, evaluation⟩ := pureProgram
  obtain ⟨bound, replay⟩ := RecoveryCompletion.evaluates_from_empty (program input) evaluation roundtrip faults
  refine ⟨bound, fun fuel enough => ?_⟩
  have direct := congrFun (Pure.evaluation_matches_direct ReplayFaults.noBlobs evaluation) ⟨[], {}⟩
  change (DirectInterpreter.interpret ReplayFaults.noBlobs program input).run.run ⟨[], {}⟩ =
    (.ok outcome, ⟨[], {}⟩) at direct
  dsimp only
  rw [direct]
  exact replay fuel enough

end LeanCloud.Proofs
