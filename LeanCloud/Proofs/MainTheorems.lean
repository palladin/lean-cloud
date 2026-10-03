import LeanCloud.Proofs.PureReplay
import LeanCloud.Proofs.QueueContract
import LeanCloud.Proofs.BackendRealization

/-!
# Main interpreter equivalence theorems

Start here to review the three guarantees for pure workflows, from the concrete
pure backend to arbitrary queues and concurrent recovery:

* `LeanCloud.Proofs.pure_replay_matches_direct`: the pure backend's deterministic
  work list and recorded locations produce the direct outcome. No fairness premise.
* `LeanCloud.Proofs.replay_matches_direct`: direct and replay evaluation agree with an
  exact Db and a lawful, fair queue whose worker steps are serialized.
* `LeanCloud.Proofs.ConcurrentRecovery.concurrent_replay_matches_direct`: concurrent replay with
  crashes and restarts eventually returns and persists the direct outcome.

All start with an empty Db and the root work item, and derive sufficient fuel.
`PureProgram` and `CodecLaw` are defined in `Assumptions.lean`; the concurrent
comparison law `RecordedComparisons` is defined in `BackendEquivalence.lean`.
The concurrent execution conditions and conclusion are spelled out below in
`FairExecution` and `ReplayMatches`. Supporting proofs remain in the imports.

The concurrent theorem uses the shared primitive service contracts in
`Backend/Contract.lean`. Its execution allows duplicate deliveries, stale
acknowledgements and requests that commit after their caller has crashed.
-/

namespace LeanCloud.Proofs
open Lean ReplayModel ReplayInterpreter.Internal

/-- The simplest equivalence theorem: pure replay with the concrete Db and
head-of-list queue equals direct evaluation. This is the ordinary location-based
interpreter; its backend and termination are proved, not supplied as hypotheses.
The scope is ordinary pure values, bind, delay, failure, and parallel. -/
theorem pure_replay_matches_direct [codec : Codec α]
    (program : ι → Cloud Id α) (input : ι)
    (pureProgram : PureProgram (program input)) (codecLaw : CodecLaw codec) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      Pure.replay fuel program input = Pure.direct program input :=
  PureReplay.resume_matches_direct program input codecLaw pureProgram (.initial _)

/-- A pure workflow has the same value or CloudError under direct evaluation
and replay with a lawful fair queue. The fuel bound may depend on the schedule.
Only the interpreter's Db and pending locations occur in the model. -/
theorem replay_matches_direct [codec : Codec α]
    (queue : LeanCloud.WorkQueue State Id) (program : ι → Cloud Id α) (input : ι)
    (law : CodecLaw codec) (supported : PureProgram (program input))
    (contract : QueueContract queue)
    (fair : ∀ trace : DriverTrace queue (codec.encode <$> program input),
      trace.states 0 = initial → WorkQueue.Fair trace.queueTrace) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      ((LeanCloud.interpret db noBlobs queue fuel program input).run initial).1 = direct (program input) := by
  obtain ⟨trace, start⟩ := contract.trace_exists (supported.map codec.encode)
  exact fair_queue_same_output queue program input law supported trace start (fair trace start)

end LeanCloud.Proofs

namespace LeanCloud.Proofs.ConcurrentRecovery
open Lean LeanCloud.Backend LeanCloud.Backend.Proofs

/-- Environment obligations for repeated execution of the actual worker
iteration. Queue fairness is required while consumers keep polling. Crashes
stop eventually; enabled commits, replies, replacements and iterations are fair.
No field assumes successful processing, a correct result, or sufficient fuel. -/
structure FairExecution (trace : Iteration.Trace traversal root count) (stableFrom : Nat) : Prop where
  startsAtRoot : trace.states 0 = Execution.initial Replay.initial
    (Array.replicate count (Iteration.program traversal root))
  workers : trace.WeaklyFair
  delivery : trace.FairDelivery
  crashesStop : ∀ worker, trace.schedule.NoCrashesAfter worker stableFrom

/-- The same physical execution, using the public interpreter and the supplied
fuel. Request ids may be renamed; operations, replies, worker generations and
shared service states correspond at every boundary. The chosen worker returns
`expected`, and the same outcome is durably stored with its lease receipt cleared.
This predicate contains an actual execution witness, not just a journal claim. -/
def ReplayMatches [codec : Codec α] (program : ι → Cloud Replay.M α) (input : ι)
    (trace : Iteration.Trace traversal (codec.encode <$> program input) count)
    (completedAt : Nat) (fuel : Nat → Nat) (worker : Fin count)
    (expected : Except CloudError α) : Prop :=
  let root := codec.encode <$> program input
  let budget := fun index => fuel index - 1
  let publicWorkers := (Array.range count).map fun index => Replay.attempt (fuel index) program input
  Fuel.entrypoints (α := α) count budget root = publicWorkers ∧
  ∃ remaining mapping final attempt,
    Fuel.Realizes trace budget completedAt remaining mapping final ∧
    final.workers[worker.val]? = some ⟨attempt, .finished (.ok (expected, ⟨(), none⟩))⟩ ∧
    Backend.Proofs.Worker.completed final.services = some (toJson (encodedOutcome expected)) ∧
    final.services = (trace.states completedAt).services

/-- Every fair concurrent execution of a pure workflow eventually records and
returns the direct interpreter's outcome, under the shared Db, queue and recovery
contracts. The finite fuel bound is derived from that execution, not assumed as
part of fairness. Each worker may have a different adequate budget.

The workflow determines `traversal` and `expected`. The schedule and chosen worker
determine `completedAt`. Every fuel assignment above the resulting bound realizes
that execution with the unchanged public replay interpreter. No provider-specific
queue implementation, ordering, exactly-once delivery or crash rollback is used. -/
theorem concurrent_replay_matches_direct [codec : Codec α]
    (program : ι → Cloud Replay.M α) (input : ι)
    (codecLaw : CodecLaw codec) (pureProgram : PureProgram (program input))
    (blobs : BlobStorage σ Replay.M)
    (comparisons : Backend.Proofs.RecordedComparisons (program input)) :
    let direct := (DirectInterpreter.interpret blobs program input).run
    let root := codec.encode <$> program input
    ∃ traversal : Nat, ∃ expected : Except CloudError α, direct = pure expected ∧
      ∀ (workerCount : Nat) (trace : Iteration.Trace traversal root workerCount) (stableFrom : Nat),
        FairExecution trace stableFrom →
        ∀ worker : Fin workerCount, ∃ completedAt, stableFrom ≤ completedAt ∧
          ∀ fuel : Nat → Nat,
            (∀ index, index < workerCount → traversal + completedAt < fuel index) →
            ReplayMatches program input trace completedAt fuel worker expected := by
  obtain ⟨tree, expansion⟩ := (pureProgram.map codec.encode).expansion
  obtain ⟨comparable, sameExit⟩ := comparisons tree expansion
  refine ⟨sizeOf tree, Backend.Proofs.Worker.expected tree,
    Backend.Proofs.direct_expected program input codecLaw blobs expansion, ?_⟩
  intro count trace stableFrom execution worker
  obtain ⟨completedAt, attempt, afterCrashes, returned, recorded⟩ :=
    Iteration.eventually_returns expansion (pureProgram.map codec.encode) comparable sameExit
      (sizeOf tree) (Nat.le_refl _) trace execution.startsAtRoot execution.workers
      execution.delivery worker stableFrom execution.crashesStop
  refine ⟨completedAt, afterCrashes, ?_⟩
  intro fuel enough
  let budget := fun index => fuel index - 1
  have remaining index (inside : index < count) : sizeOf tree + completedAt ≤ budget index := by
    have bound := enough index inside
    dsimp [budget]
    omega
  obtain ⟨left, mapping, final, ran, durable, result⟩ := Fuel.realizes_return (α := α)
    expansion (pureProgram.map codec.encode) comparable sameExit (sizeOf tree) (Nat.le_refl _)
    trace execution.startsAtRoot completedAt budget remaining worker attempt returned
  refine ⟨?_, left, mapping, final, attempt, ran, result, ?_, durable⟩
  · apply Array.ext
    · simp [Fuel.entrypoints]
    · intro index firstInside secondInside
      have inside : index < count := by simpa [Fuel.entrypoints] using firstInside
      have equal : budget index + 1 = fuel index := by
        have bound := enough index inside
        dsimp [budget]
        omega
      dsimp only [budget] at equal
      simp [Fuel.entrypoints, Fuel.loop, Replay.attempt, LeanCloud.interpret, equal]
  · rw [durable]
    have encoded := Backend.Proofs.expected_exit program input codecLaw expansion
    exact recorded.trans (congrArg (fun outcome => some (toJson outcome)) encoded.symm)

end LeanCloud.Proofs.ConcurrentRecovery
