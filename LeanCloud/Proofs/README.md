# Interpreter semantics

Start with [MainTheorems.lean](MainTheorems.lean). It contains three theorems:

- `sequential_replay_matches_direct`
- `parallel_replay_matches_direct`
- `restarting_parallel_replay_matches_direct`

All say: the same pure program and input produce the same result under direct
evaluation and replay from empty storage, for every sufficiently large fuel
budget. Results include application errors as well as successful values.
The third theorem permits arbitrary finite worker fault scripts, including
crashes after writes commit but before the worker receives the result.

## What the assumptions mean

`Pure.Evaluation (program input) outcome` describes a finite pure evaluation of
the original Cloud program: values, delays, failures, delayed pure computations,
and parallel groups. It excludes arbitrary IO and user blob effects. The
existential assumption supplies a finite evaluation; it does not supply a replay
execution, a populated journal, or a successful result.

`Pure.RoundTrips codec` says decoding an encoded result returns that result.
The evaluation also checks codecs used at intermediate replay boundaries.

The proof constructs a sufficient fuel bound from the finite evaluation. The
caller does not have to guess the bound correctly for the theorem to hold; an
executable run with too little fuel may still return an interpreter error.

## The two replay drivers

[SequentialReplay](../SequentialReplay.lean) finishes children in source order,
passing the updated journal from one child to the next.

[ParallelReplay](../ParallelReplay.lean) starts all children with `Task.spawn`.
Each reads the same immutable journal and returns only its new records. The
parent takes their disjoint union and resumes after all children finish.
Any overlapping write is rejected, including identical values. The proof
establishes that siblings write different locations. Application
errors are collected in source order, just like the direct interpreter.

Both drivers call the actual `ReplayInterpreter.step`. Reconstruction follows
the branch's location; recorded values restore continuations, missing commands
execute and record, and incomplete parallel groups suspend. After child records
are available, the same interpreter records the join and final return.

The only model state is a list of replay records in
[ReplayModel](../ReplayModel.lean). Direct evaluation leaves it untouched. The
proof compares results, not the physical order of journal entries.

In Lean's logic, `(Task.spawn f).get` reduces to `f ()`. Compiled execution uses
asynchronous tasks. The proof establishes replay and merge semantics; it does
not model thread scheduling or prove operating-system progress.

## Worker-local recovery

[RestartingParallelReplay](../ReplayRecovery.md) adds local worker crashes to the
same interpreter. Workers retry inside their spawned functions and return their
recorded outcomes. Scheduling only handles replies; it has no journal operations
or crash mechanism.

[WorkerRecovery.lean](WorkerRecovery.lean) lifts atomic crash laws over entire
worker attempts. [RecoveryWorker.lean](RecoveryWorker.lean) proves that restarting
the actual interpreter step preserves committed records and eventually returns
a correct reply, including the final result read. Each worker writes only its
own region. [RecoveryBatch.lean](RecoveryBatch.lean) verifies the disjoint union
of those writes.

[RecoveryDriver.lean](RecoveryDriver.lean) proves completion of the whole driver.
Descending to children reduces the remaining tree depth; resuming their parent
follows at least one previously missing child result becoming durable. A finite
pure evaluation bounds both the depth and the number of records. Together with
finite fault scripts, this supplies a sufficient fuel budget without assuming
that replay already succeeds.

The third public theorem compares the original program in the worker monad with
direct evaluation of that same program. Its outer `match` rules out a crash in
the direct pure evaluation; `expected` includes both successful values and
application errors. It does not assert scheduler recovery, eventual service
availability, arbitrary IO equivalence, or OS task scheduling progress.

## Proof structure

| File | Purpose |
| --- | --- |
| [Pure.lean](Pure.lean), [Direct.lean](Direct.lean) | Pure workflow meaning agrees with direct interpretation. |
| [Location.lean](Location.lean), [JournalRegion.lean](JournalRegion.lean) | Locations identify separate command, return, sibling, and descendant records. |
| [Specification.lean](Specification.lean) | Construct the expected records from a finite pure evaluation. These records are a proof witness, never runtime input. |
| [ProgramCursor.lean](ProgramCursor.lean), [ReplayCursor.lean](ReplayCursor.lean) | Reconstruct the right typed continuation from recorded prefixes. |
| [Recording.lean](Recording.lean), [Results.lean](Results.lean), [Parallel.lean](Parallel.lean) | Execute missing commands, preserve records, and join results in source order. |
| [JournalMerge.lean](JournalMerge.lean) | Workers preserve the old journal and return fresh records in disjoint regions; union preserves all results. |
| [ReplayExecution.lean](ReplayExecution.lean), [ReplayCompletion.lean](ReplayCompletion.lean) | One shared completion proof, with sequential and parallel batch cases. |
| [WorkerRestart.lean](WorkerRestart.lean), [WorkerRecovery.lean](WorkerRecovery.lean) | Atomic before/after faults and whole-attempt retry laws. |
| [RecoveryMeaning.lean](RecoveryMeaning.lean), [RecoveryCursor.lean](RecoveryCursor.lean), [RecoveryPrefix.lean](RecoveryPrefix.lean) | Bound replay paths and recover their typed continuations across interruptions. |
| [RecoveryStep.lean](RecoveryStep.lean), [RecoveryReads.lean](RecoveryReads.lean), [RecoveryReplay.lean](RecoveryReplay.lean), [RecoveryWorker.lean](RecoveryWorker.lean) | Verify actual worker execution and local restart. |
| [RecoveryBatch.lean](RecoveryBatch.lean), [RecoveryProgress.lean](RecoveryProgress.lean), [RecoveryDriver.lean](RecoveryDriver.lean), [RecoveryCompletion.lean](RecoveryCompletion.lean) | Merge isolated writes, establish progress, and finish from empty storage with finite worker faults. |

[ProofExamples.lean](../../LeanCloudTests/ProofExamples.lean) applies all three public
theorems to a workflow with captured values, delays, and nested parallel groups.
Build the proofs with `lake build`.

## Runtime validation

Actors, mailboxes, leases, scheduler recovery, and deployment policies belong to
the runtime implementation and its tests. Worker-local interruption at atomic
storage boundaries is the crash model covered by the third semantic theorem.

[Sim](../Simulation.md) remains available to test scheduler/worker coordination
and failure recovery. [Runtime tests](../../LeanCloudTests/README.md) compare the
same interpreter against model and real backends, including durable storage,
message delivery, multi-run isolation, and process controls. Passing those tests
provides implementation evidence rather than a universal deployment theorem.
Source annotations and observer behavior are covered by
[Source tests](../../LeanCloudTests/Source.lean).
