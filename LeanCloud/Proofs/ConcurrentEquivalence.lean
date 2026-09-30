import LeanCloud.Proofs.ConcurrentAudit
import LeanCloud.Proofs.SimulationEvaluation
import LeanCloud.Proofs.ConcurrentRealization

/-! `same_output` is the main equivalence theorem for pure concurrent workflows.
Fair execution supplies a completing prefix and sufficient finite fuel for the
public replay interpreter. The supporting theorems below it describe safety and
attempt termination when fuel may be insufficient. -/

namespace LeanCloud.Proofs.ConcurrentRecovery
open Lean Simulation SimulationBackend ReplayRecovery ConcurrentQueue

/-- Equality tests recognize the values this workflow records. This is a law
about serialization comparisons, not an assumption that replay is correct. -/
def RecordedComparisons [codec : Codec α] (program : Cloud M α) : Prop :=
  ∀ tree, Expansion (codec.encode <$> program) tree →
    Comparable (tree.journal Location.root) ∧
    ∀ location node, (location, node) ∈ tree.nodes Location.root →
      (node.exit == node.exit) = true

/-- A legal repeated execution starts with the root work item. Enabled workers
and retained queue items are treated fairly, and crashes stop at `stableFrom`.
None of these fields assumes completion, a correct result, or enough loop fuel. -/
structure FairExecution
    (trace : ConcurrentRepeated.RawTrace duration traversal root count)
    (stableFrom : Nat) : Prop where
  startsAtRoot : trace.states 0 = Simulation.State.initial SimulationBackend.initial
    (fun _ : Fin count => ConcurrentRepeated.rawIteration duration traversal root)
  workers : trace.WeaklyFair
  delivery : ConcurrentRepeated.FairDelivery trace
  crashesStop : ∀ worker, trace.NoCrashesAfter worker stableFrom

/-- Execute the trace's physical events using the public replay interpreter.
The chosen worker must return `expected`, and that same outcome must be durably
stored. Its local receipt is cleared and its durable state matches the trace.
An illegal event, missing result, or absent completion record fails this
predicate. Only administrative iteration boundaries are erased from the trace. -/
def ReplayMatches [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    (trace : ConcurrentRepeated.RawTrace duration traversal (codec.encode <$> program input) count)
    (completedAt : Nat) (fuel : Fin count → Nat) (worker : Fin count)
    (expected : Except CloudError α) : Prop :=
  let encoded : Exit := match expected with
    | .ok value => .success (codec.encode value)
    | .error error => .failure error
  let start := fun index =>
    let replay := LeanCloud.interpret SimulationBackend.db SimulationBackend.noBlobs
      (queue duration) (fuel index) program input
    replay.run ⟨(), none⟩
  let events := ConcurrentFuel.eventsBefore trace completedAt
  let initial := Simulation.State.initial SimulationBackend.initial start
  match Simulation.run start SimulationBackend.advance events initial with
  | .error _ => False
  | .ok final =>
    match (final.workers worker).outcome? with
    | none => False
    | some (actual, localState) =>
      actual = expected ∧
      final.durable.completed = some encoded ∧
      localState = ⟨(), none⟩ ∧
      final.durable = (trace.states completedAt).durable

private theorem direct_expected [codec : Codec α] (program : ι → Cloud M α) (input : ι)
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
private theorem expected_exit [codec : Codec α] (program : ι → Cloud M α) (input : ι)
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

/-- The direct interpreter determines `expected` once, independently of the
schedule. Every fair execution eventually gives each worker that exact result,
with the same outcome durably recorded, when replayed with sufficient finite fuel.

Quantifier order matters: `traversal` and `expected` depend only on the workflow;
`completedAt` may depend on the schedule and worker. Every per-worker fuel
assignment above the explicit bound works. Completion is proved, not assumed.
`ReplayMatches` runs the public interpreter and requires both the returned result
and its persisted encoding, as well as the durable-state match. -/
theorem same_output [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    (codecLaw : CodecLaw codec) (pureProgram : PureProgram (program input))
    (blobs : BlobStorage σ M)
    (comparisons : RecordedComparisons (program input)) :
    let direct := (DirectInterpreter.interpret blobs program input).run
    let root := codec.encode <$> program input
    ∃ traversal : Nat, ∃ expected : Except CloudError α, direct = pure expected ∧
      ∀ (leaseDuration workerCount : Nat)
        (trace : ConcurrentRepeated.RawTrace leaseDuration traversal root workerCount)
        (stableFrom : Nat),
        FairExecution trace stableFrom →
        ∀ worker, ∃ completedAt, stableFrom ≤ completedAt ∧
          ∀ fuel : Fin workerCount → Nat,
            (∀ index, traversal + completedAt < fuel index) →
            ReplayMatches program input trace completedAt fuel worker expected := by
  obtain ⟨tree, expansion⟩ := (pureProgram.map codec.encode).expansion
  obtain ⟨comparable, sameExit⟩ := comparisons tree expansion
  refine ⟨sizeOf tree, ConcurrentQueue.expected tree, direct_expected program input codecLaw blobs expansion, ?_⟩
  intro duration count trace stableFrom execution worker
  obtain ⟨completedAt, afterCrashes, returned, recorded⟩ := ConcurrentRepeated.eventually_returns expansion (pureProgram.map codec.encode)
    comparable sameExit duration (sizeOf tree) (Nat.le_refl _) trace execution.startsAtRoot
    execution.workers execution.delivery stableFrom execution.crashesStop worker
  refine ⟨completedAt, afterCrashes, ?_⟩
  intro fuel enough
  let budget := fun index => fuel index - 1
  have remaining index : sizeOf tree + completedAt ≤ budget index := by
    have bound := enough index
    dsimp [budget]
    omega
  have sameFuel index : budget index + 1 = fuel index := by
    have bound := enough index
    dsimp [budget]
    omega
  obtain ⟨final, ran, durable, result⟩ := ConcurrentFuel.realizes_return (α := α) expansion (pureProgram.map codec.encode)
    comparable sameExit duration (sizeOf tree) (Nat.le_refl _) trace execution.startsAtRoot
    completedAt budget remaining worker returned
  unfold ReplayMatches
  dsimp only [LeanCloud.interpret]
  simp only [ConcurrentFuel.loop, sameFuel] at ran
  have stored : final.durable.completed = some tree.exit := by rw [durable]; exact recorded
  simpa only [ran, result, expected_exit program input codecLaw expansion, true_and] using
    And.intro stored durable

/-- Safety for any fuel budget: a returned result is correct or exhausted.
`same_output` additionally proves completion and derives sufficient fuel.
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
`same_output` additionally derives a completing prefix under fairness. -/
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
`same_output` derives enough fuel for workflow completion under fair delivery. -/
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
