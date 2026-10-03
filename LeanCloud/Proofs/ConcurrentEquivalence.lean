import LeanCloud.Proofs.ConcurrentAudit
import LeanCloud.Proofs.SimulationEvaluation
import LeanCloud.Proofs.ConcurrentRealization

/-! Supporting results for concurrent interpreter equivalence: direct evaluation,
serialization, output safety, and attempt termination with arbitrary fuel.
The main `concurrent_replay_matches_direct` theorem and its execution contract are in
`MainTheorems.lean`. -/

namespace LeanCloud.Proofs.ConcurrentRecovery
open Lean Simulation SimulationBackend ReplayRecovery ConcurrentQueue

/-- Equality tests recognize the values this workflow records. This is a law
about serialization comparisons, not an assumption that replay is correct. -/
def RecordedComparisons [codec : Codec α] (program : Cloud M α) : Prop :=
  ∀ tree, Expansion (codec.encode <$> program) tree →
    Comparable (tree.journal Location.root) ∧
    ∀ location node, (location, node) ∈ tree.nodes Location.root →
      (node.exit == node.exit) = true

theorem direct_expected [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    (law : CodecLaw codec) (blobs : BlobStorage σ M) {tree : ExecutionTree}
    (expansion : Expansion (codec.encode <$> program input) tree) :
    (DirectInterpreter.interpret blobs program input).run = pure (ConcurrentQueue.expected tree) := by
  obtain ⟨outcome, evaluated, encoded⟩ := expansion.evaluation.map_cases (program input) codec.encode
  have decoded : ConcurrentQueue.expected (α := α) tree = outcome := by
    unfold ConcurrentQueue.expected ExecutionTree.exit
    rw [encoded]
    cases outcome with
    | error error => rfl
    | ok value =>
      change (ReplayInterpreter.Internal.decode (m := Id) codec (codec.encode value)).run = .ok value
      simp only [ReplayInterpreter.Internal.decode, law value]
      rfl
  rw [decoded]
  exact evaluated.simulation blobs

/-- The expected result's encoding is exactly the outcome persisted by replay,
including workflow errors. Codec failure cannot stand in for a stored failure. -/
theorem expected_exit [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    (law : CodecLaw codec) {tree : ExecutionTree}
    (expansion : Expansion (codec.encode <$> program input) tree) :
    (match ConcurrentQueue.expected (α := α) tree with
      | .ok value => Exit.success (codec.encode value)
      | .error error => .failure error) = tree.exit := by
  obtain ⟨outcome, _, encoded⟩ := expansion.evaluation.map_cases (program input) codec.encode
  unfold ConcurrentQueue.expected ExecutionTree.exit
  rw [encoded]
  cases outcome with
  | error error => rfl
  | ok value =>
    change (match (ReplayInterpreter.Internal.decode (m := Id) codec (codec.encode value)).run with
      | .ok value => Exit.success (codec.encode value)
      | .error error => .failure error) = Exit.success (codec.encode value)
    simp only [ReplayInterpreter.Internal.decode, law value]
    rfl

/-- Safety for any fuel budget: a returned result is correct or exhausted.
`concurrent_replay_matches_direct` additionally proves completion and derives sufficient fuel.
The trace runs the actual interpreter with independent crashes and restarts. -/
theorem output_safety [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    (codecLaw : CodecLaw codec) (pureProgram : PureProgram (program input))
    (blobs : BlobStorage σ M)
    (comparisons : RecordedComparisons (program input)) :
    let direct := (DirectInterpreter.interpret blobs program input).run
    ∃ expected : Except CloudError α, direct = pure expected ∧
      ∀ (leaseDuration workerCount : Nat) (fuel : Fin workerCount → Nat),
        let start := fun worker => attempt (fuel worker) leaseDuration program input
        let initial := Simulation.State.initial SimulationBackend.initial start
        ∀ events final,
          Simulation.run start SimulationBackend.advance events initial = .ok final →
          ∀ worker actual localState,
            (final.workers worker).outcome? = some (actual, localState) →
            actual = expected ∨ actual = .error ConcurrentQueue.exhausted := by
  obtain ⟨tree, expansion⟩ := (pureProgram.map codec.encode).expansion
  obtain ⟨comparable, sameExit⟩ := comparisons tree expansion
  refine ⟨ConcurrentQueue.expected tree, direct_expected program input codecLaw blobs expansion, ?_⟩
  intro duration count fuel
  dsimp only
  intro events final executed worker actual localState finished
  have safe := (attempts_safe program input expansion pureProgram comparable sameExit duration fuel events final executed).2.2
  exact safe worker (actual, localState) finished

/-- Agreement whenever a given finite prefix returns with enough fuel.
`concurrent_replay_matches_direct` additionally derives a completing prefix under fairness. -/
theorem output_agreement [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    (codecLaw : CodecLaw codec) (pureProgram : PureProgram (program input))
    (blobs : BlobStorage σ M)
    (comparisons : RecordedComparisons (program input)) :
    let direct := (DirectInterpreter.interpret blobs program input).run
    ∃ traversal : Nat, ∃ expected : Except CloudError α, direct = pure expected ∧
      ∀ (leaseDuration workerCount : Nat) (fuel : Fin workerCount → Nat),
        let start := fun worker => attempt (fuel worker) leaseDuration program input
        let initial := Simulation.State.initial SimulationBackend.initial start
        ∀ events final,
          Simulation.run start SimulationBackend.advance events initial = .ok final →
          ∀ worker actual localState,
            traversal + events.length < fuel worker →
            (final.workers worker).outcome? = some (actual, localState) →
            actual = expected := by
  obtain ⟨tree, expansion⟩ := (pureProgram.map codec.encode).expansion
  obtain ⟨comparable, sameExit⟩ := comparisons tree expansion
  refine ⟨sizeOf tree, ConcurrentQueue.expected tree, direct_expected program input codecLaw blobs expansion, ?_⟩
  intro duration count fuel
  dsimp only
  intro events final executed worker actual localState enough finished
  obtain ⟨past, _, _, length, bounded⟩ := ConcurrentAudit.attempts_certified program input expansion pureProgram
    comparable sameExit duration fuel events final executed
  rcases bounded worker (actual, localState) finished with correct | ⟨_exhausted, short⟩
  · exact correct
  · simp only [Nat.add_zero] at short
    omega

/-- Attempt termination for any fuel budget, once this worker's crashes stop
and its actions are scheduled fairly. Its result may be fuel exhaustion.
`concurrent_replay_matches_direct` derives enough fuel for workflow completion under fair delivery. -/
theorem eventual_output [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    (codecLaw : CodecLaw codec) (pureProgram : PureProgram (program input))
    (blobs : BlobStorage σ M)
    (comparisons : RecordedComparisons (program input)) :
    let direct := (DirectInterpreter.interpret blobs program input).run
    ∃ expected : Except CloudError α, direct = pure expected ∧
      ∀ (leaseDuration workerCount : Nat) (fuel : Fin workerCount → Nat),
        let start := fun worker => attempt (fuel worker) leaseDuration program input
        let initial := Simulation.State.initial SimulationBackend.initial start
        ∀ trace : Simulation.Trace start SimulationBackend.advance,
          trace.states 0 = initial → trace.WeaklyFair →
          ∀ worker stableFrom, trace.NoCrashesAfter worker stableFrom →
            ∃ completedAt actual localState,
              stableFrom ≤ completedAt ∧
              (trace.states completedAt).workers worker = .finished (actual, localState) ∧
              (actual = expected ∨ actual = .error ConcurrentQueue.exhausted) := by
  obtain ⟨outcome, direct, answers⟩ := output_safety program input codecLaw pureProgram blobs comparisons
  obtain ⟨tree, expansion⟩ := (pureProgram.map codec.encode).expansion
  obtain ⟨comparable, sameExit⟩ := comparisons tree expansion
  refine ⟨outcome, direct, ?_⟩
  intro duration count fuel
  dsimp only
  intro trace initialized fair worker cut noCrash
  obtain ⟨later, ⟨actual, localState⟩, after, finished, _⟩ := attempts_return program input expansion pureProgram comparable sameExit
    duration fuel trace initialized fair worker cut noCrash
  have executed := trace.run_prefix later
  rw [initialized] at executed
  exact ⟨later, actual, localState, after, finished,
    answers duration count fuel _ _ executed worker actual localState (by rw [finished]; rfl)⟩

end LeanCloud.Proofs.ConcurrentRecovery
