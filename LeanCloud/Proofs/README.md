# Interpreter equivalence

Two theorems compare the actual replay and direct interpreters:

| Theorem | Backend and execution model |
| --- | --- |
| [`LeanCloud.Proofs.same_output`](QueueContract.lean) | An exact Db map and a fair queue with atomic acknowledgement. |
| [`SharedRecovery.same_output`](RecoveryEquivalence.lean) | The physical immutable journal and leased queue, with finite crashes and `CrashM.restart`. Publication and acknowledgement are separate operations. |

Both start with an empty Db and the root work item. They prove equality of the
returned value or `CloudError` for the same program and input. They derive eventual
completion and sufficient fuel; a successful replay execution is not a premise.
The recovery theorem also derives a sufficient retry budget.

The direct interpreter performs no backend operations for the supported fragment.
The theorems compare outputs, without requiring equal final storage, effect
histories, or an external user world.

The recovery theorem states the common outcome explicitly: direct evaluation of
the original program is `pure outcome`, and replay returns `.ok outcome` with
sufficient fuel and retries. The outer `.ok` means recovery has returned; `outcome`
itself is an `Except CloudError α`. The direct side needs no initial durable state
or backend conversion. `journalMap.program` remains an internal model conversion
on the replay side, embedding the journal-only program in the combined backend.

## Scope and assumptions

- **Pure workflows:** ordinary `pure`/`return`, bind, `delay`, `fail`, and `parallel`,
  including nested and empty groups. [`PureProgram`](Assumptions.lean) checks
  continuations for every possible argument. Runtime exec, blobs, choice, and
  cancellation are excluded. The recorded `Cloud.pure (fun _ => value)` helper
  uses exec and is also outside this fragment.
- **Lawful codecs:** every parallel codec and the final result codec must decode
  its own encoding to the original value. Results and failure priority follow
  array positions regardless of delivery order.
- **Serialized attempts:** one worker attempt runs at a time. A restart keeps the
  journal, queue, completion record, and remaining fault script, but creates a
  fresh worker handle. This does not prove correctness of simultaneous workers.
- **Finite crashes:** the recovery model allows interruption before or after each
  primitive operation. A committed write survives a crash after commit. Fault
  scripts are finite and are not reset by retries.
- **Fair delivery and time:** retained work must eventually be delivered unless
  the workflow completes first. The environment advances time before polling;
  fairness includes eventual lease availability. No particular clock policy or
  real service is proved fair here.
- **Comparison laws:** the recovery theorem explicitly requires reflexivity of
  JSON and `Exit` comparisons on the program's recorded values. Lean's JSON
  comparison uses a `partial` definition, so there is no assumed general
  `LawfulBEq Json` instance or custom axiom discharging this condition.

Fuel bounds may depend on the delivery schedule and faults. For every sufficiently
large interpreter budget, the recovery theorem supplies a retry bound above which
replay returns the direct interpreter's outcome. It does not promise a uniform
latency bound for every fair schedule.

## Reading the proof

Start with [RecoveryEquivalence.lean](RecoveryEquivalence.lean), which connects
the public `LeanCloud.interpret` and `DirectInterpreter.interpret` calls.
`Trace.run_eventually_restart` supplies recovery from a valid, covered starting state.
The underlying argument has five parts:

1. **Pure semantics and program structure.** [Evaluation.lean](Evaluation.lean)
   gives the direct meaning of the supported fragment. [ExecutionTree.lean](ExecutionTree.lean)
   derives a finite tree from that evaluation. This is proof data, not another
   interpreter. [TreeRecords.lean](TreeRecords.lean) and [TreeJournal.lean](TreeJournal.lean)
   derive the permissible physical records from the tree.
2. **Storage and worker safety.** [JournalRecovery.lean](JournalRecovery.lean)
   and [CrashSpec.lean](CrashSpec.lean) track committed prefixes through individual
   raw reads and writes using one compositional crash specification.
   [CompletionView.lean](CompletionView.lean) proves the shared save-or-reuse
   completion rule for root and child commands. [TreeActivation.lean](TreeActivation.lean) derives replay
   prerequisites from durable records. [TreeTargetStep.lean](TreeTargetStep.lean)
   proves safety of the actual worker, including obsolete duplicate deliveries.
   [WorkerCases.lean](WorkerCases.lean) gives safety, coverage, and progress one
   shared verification rule for reconstruction, typed decoding, and obsolete
   deliveries. Each supplies only its completion, initialization, join, and
   missing-child obligations.
3. **No lost work.** [TreeCoverage.lean](TreeCoverage.lean) represents an unfinished
   branch by a retained message, its children, or its continuation.
   [CoveragePublication.lean](CoveragePublication.lean) preserves this coverage
   through interrupted publication. [SharedCoverage.lean](SharedCoverage.lean)
   and [SharedLoop.lean](SharedLoop.lean) compose polling, worker execution, and
   publication, preserving coverage and journal growth together in the shared state.
4. **Eventual completion.** [SharedTrace.lean](SharedTrace.lean) proves that finite
   faults eventually stop and the finite immutable journal stabilizes.
   [StableProgress.lean](StableProgress.lean) and [StableWorker.lean](StableWorker.lean)
   show that a delivered location then completes a branch or exposes smaller
   program structure. [SharedLiveness.lean](SharedLiveness.lean) combines this
   with coverage and fair delivery to prove eventual completion and return.
5. **Public execution and recovery.** [ReplayFuel.lean](ReplayFuel.lean) and
   [SharedFuel.lean](SharedFuel.lean) show that sufficient traversal budgets give
   identical observations, including crashes and committed state.
   [ClockedReplay.lean](ClockedReplay.lean) connects environment time to those
   observations. [RestartExecution.lean](RestartExecution.lean) proves that the
   public loop executes their finite prefix: unfinished iterations decrease fuel,
   while a crash restarts with the original budget. The result codec then connects
   the recovered outcome to direct evaluation.

The earlier atomic-backend proof follows a separate route through
[ReplaySnapshot.lean](ReplaySnapshot.lean), [SnapshotStep.lean](SnapshotStep.lean),
[FairDriver.lean](FairDriver.lean), and [QueueContract.lean](QueueContract.lean).
It shares the pure semantics, codecs, and location laws with the recovery proof.

## Backend model

[SharedRecovery.lean](SharedRecovery.lean) combines the journal, leased transport,
and final outcome in one durable state with one fault script. Embedding the
components preserves their individual crash boundaries; it does not turn a
publication sequence into a transaction.

[JournalDb](../JournalDb.lean) stores a fork descriptor and immutable result and
child-slot records. Reads reconstruct the logical group result. Child publication
precedes the optional completed-group cache, so retries can read a completed group
without that cache. Compatible writes preserve previously recorded outcomes.

[LeasePublication.lean](LeasePublication.lean) reasons about the actual lease
adapter. Each message has its own slot, including duplicates of a location. The
adapter publishes successors or the final outcome before acknowledging the
incoming receipt. A crash can repeat publication, but cannot discard the last
representation of unfinished work. A committed dequeue whose reply is lost leaves
a leased message that becomes eligible again after expiry.

The lease model validates receipts strictly. Renewal and redelivery rotate the
receipt; stale acknowledgements cannot remove a newer delivery. These are ideal
primitive guarantees, not claims already proved for SQLite, PostgreSQL, Azure,
or AWS. Refinement to real services and simultaneous-worker correctness remain
outside the theorems.

Useful independent interface laws remain in [Codecs.lean](Codecs.lean),
[JournalDb.lean](JournalDb.lean), [LeaseQueue.lean](LeaseQueue.lean), and
[Crash.lean](Crash.lean): codec round trips, independence of sibling record writes,
lease behavior, crash boundaries, and restart soundness.

## Verification

Run `lake build` and `lake test`. The proofs contain no `sorry` or custom axioms.
To inspect the main theorems' logical dependencies in Lean:

```lean
import LeanCloud.Proofs

#print axioms LeanCloud.Proofs.same_output
#print axioms LeanCloud.Proofs.SharedRecovery.same_output
```

Both use only Lean's standard axioms: `propext`, `Classical.choice`, and `Quot.sound`.
