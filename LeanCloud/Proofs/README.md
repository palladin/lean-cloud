# Interpreter equivalence

Two theorems compare the actual replay and direct interpreters:

| Theorem | Backend and execution model |
| --- | --- |
| [`LeanCloud.Proofs.same_output`](QueueContract.lean) | An exact Db map and a fair queue with atomic acknowledgement. |
| [`ConcurrentRecovery.same_output`](ConcurrentEquivalence.lean) | Any finite number of interleaved workers sharing the journal and leased queue, with saved replies and independent crashes/restarts. |

All start with an empty Db and the root work item. They prove equality of the
returned value or `CloudError` for the same program and input. They derive eventual
completion and sufficient fuel; a successful replay execution is not a premise.

The concurrent theorem starts from any fair repeated-worker trace whose crashes
eventually stop. For each worker it derives a completing prefix `atTime`. Every
per-worker fuel assignment satisfying `traversal + atTime < fuel worker` realizes
that prefix in the public interpreter with the exact direct result, durably
stored as well as returned. Only
administrative iteration boundaries disappear; commits, saved-reply deliveries,
crashes, restarts, clock advances, and durable changes stay the same.

The main statement uses three names, all defined next to it:

- `RecordedComparisons`: equality tests recognize the workflow's recorded JSON
  values and exits. This is a serialization law, not output agreement.
- `FairExecution`: start with the root item, fairly schedule workers and retained
  deliveries, and stop crashing after `stableFrom`. It assumes no successful run.
- `ReplayMatches`: run the public interpreter on that trace's physical events;
  require the chosen worker to return `expected` and the final durable completion
  record to contain its exact encoding. The worker clears its receipt and produces
  the trace's durable state. An illegal event, absent result, or missing completion
  record makes it false.

`same_output` appears before the supporting theorems. Local bindings name the
direct evaluation, encoded root, worker entry point, and initial state where
needed. Returned results are named `actual`; `expected` is the direct result.
The later `output_safety` and `eventual_output` lemmas accept arbitrary fuel and
therefore allow exhaustion. The main theorem derives enough fuel for exact equality.

Read the conclusion in this order (this is an outline, with types omitted):

```text
There are traversal and expected such that:
  direct(program, input) = expected
  for every fair execution and every worker:
    there is a completedAt after crashes stop such that:
      for every fuel assignment above traversal + completedAt:
        replay(the same physical events).result(worker) = expected
        final.durable.completed = some (encode expected)
```

Here `encode expected` means `.success (codec.encode value)` for `.ok value`,
or `.failure error` for `.error error`. This compares the stored record itself;
a missing record or an invalid value that merely decodes to an error cannot
stand in for the expected workflow outcome. The completion record is separate
from the per-location journal records, and both belong to durable storage.

`expected` is chosen before the execution: changing branch order, delays, crashes,
or retries cannot change it. `completedAt` is derived after the execution is
chosen: completion is a conclusion. Fuel is chosen last, with an explicit bound,
and every larger assignment works. A fair schedule can delay work arbitrarily
long, so the theorem makes no claim that one fixed budget covers all schedules.

For example, let a pure workflow run `input + 1` and `2 * input` in parallel and
return their pair. For input `10`, direct evaluation returns `.ok (11, 20)`.
Concurrent replay must eventually return that same ordered pair under the stated
conditions, even if the second child finishes first or a worker crashes after
publishing a child result. If the workflow instead fails, the equality covers
the exact `CloudError`, including the direct interpreter's array-order failure
priority. These are consequences for supported workflows with lawful codecs and
comparisons; arbitrary `IO` actions are outside the theorem.

The physical-event and durable-state match prevents the proof from switching to
a different convenient execution. It compares replay with its trace, not with
the direct interpreter's storage. Real backend implementations and the fairness
of a particular deployment scheduler still need their own justification.

The direct interpreter performs no backend operations for the supported fragment.
The theorems compare outputs, without requiring equal final storage, effect
histories, or an external user world.

## Scope and assumptions

- **Pure workflows:** ordinary `pure`/`return`, bind, `delay`, `fail`, and `parallel`,
  including nested and empty groups. [`PureProgram`](Assumptions.lean) checks
  continuations for every possible argument. Exec, blobs, choice, cancellation,
  and the recorded `Cloud.pure` helper are outside this fragment.
- **Lawful codecs:** parallel and final-result codecs decode their own encodings.
  Results and failure priority follow array positions regardless of delivery order.
- **Atomic primitives:** each physical Db get/put, enqueue/dequeue/acknowledgement,
  and completion-record access is individually atomic. A multi-key read or
  publication is not a transaction.
- **Fair execution:** enabled worker actions and iteration repetition are weakly
  fair. Retained work is eventually delivered unless acknowledged or the workflow
  completes first. Crashes eventually stop. Fair delivery includes eventual lease
  availability; the driver advances time explicitly.
- **Comparison laws:** `RecordedComparisons` requires reflexive JSON and `Exit`
  equality on this workflow's recorded values. Lean's partial JSON equality does
  not provide a general `LawfulBEq Json` instance, so the condition is explicit.

The fuel bound depends on the completing prefix. There is no fixed latency or
fuel budget that covers every fair schedule. Real backend implementations and
deployment fairness remain outside the model.

## One execution model

[`SimM`](../Simulation.lean) represents atomic requests. Its external driver
keeps shared durable state and a separate suspended continuation for each worker.
`commit` changes durable state and saves a reply; `resume` delivers that reply.
A crash drops the continuation and reply, and restart creates a fresh attempt.
Neither changes durable records, releases leases, or advances time.

[SimulationBackend.lean](../SimulationBackend.lean) runs the actual replay
interpreter over the actual `JournalDb` and `LeaseQueue.toWorkQueue` adapters.
The same backend is used for single-worker recovery and concurrent tests.

`JournalDb` stores fork descriptors, child outcomes, and optional completed-result
caches under separate keys. It reconstructs partial results from those records.
Compatible writes preserve old values; a delayed read can combine observations
from different times. The ideal raw Db's write log supplies proof history while
lookup retains the ordinary key/value interface.

The queue retains messages until acknowledgement. Each delivery has a receipt;
redelivery and renewal rotate it, so stale acknowledgements cannot delete a newer
delivery. The adapter publishes successor locations or the final outcome before
acknowledging the incoming message. Lost replies can produce duplicates, but the
proof shows unfinished work cannot lose its last representation.

## Reading the proof

Start at [`ConcurrentRecovery.same_output`](ConcurrentEquivalence.lean). The
supporting argument proceeds through these parts:

1. [Evaluation](Evaluation.lean) gives the pure program's direct meaning.
   [ExecutionTree](ExecutionTree.lean), [TreeRecords](TreeRecords.lean), and
   [TreeJournal](TreeJournal.lean) derive its finite structure and permitted records.
2. [SimulationSafety](SimulationSafety.lean) handles waiting operations and saved
   replies while other workers change shared state. [ConcurrentJournal](ConcurrentJournal.lean)
   and [ConcurrentRead](ConcurrentRead.lean) prove compatible publication and
   reconstruction through separate physical calls.
3. [ConcurrentFinish](ConcurrentFinish.lean), [ConcurrentWakeup](ConcurrentWakeup.lean),
   and [ConcurrentStep](ConcurrentStep.lean) prove child completion, parent wakeup,
   and the actual location-based replay step. [ConcurrentLoop](ConcurrentLoop.lean)
   composes these with leased polling and publication.
4. [ConcurrentAudit](ConcurrentAudit.lean) connects each acknowledgement to a real
   delivery and published replacement work. [ConcurrentNoLoss](ConcurrentNoLoss.lean)
   proves every finite schedule has either the correct durable final result or
   outstanding work. [ConcurrentRank](ConcurrentRank.lean) rules out cycles once
   the finite journal stabilizes.
5. [ConcurrentRepeated](ConcurrentRepeated.lean) provides a proof-only view of
   continued polling. [ConcurrentDelivery](ConcurrentDelivery.lean) connects fair
   dequeue selection to actual processing. [ConcurrentCompletion](ConcurrentCompletion.lean)
   proves eventual durable completion and each worker's return after crashes stop.
6. [ConcurrentRealization](ConcurrentRealization.lean) runs that completing prefix
   through the public fuel-based interpreter. It removes only administrative
   repetition events; physical operations, replies, crashes, restarts, and clock
   advances keep their order and effects.

[`ReplayIteration.iteration`](ReplayIteration.lean) factors one actual
poll/process/publish iteration. [ConcurrentIteration](ConcurrentIteration.lean)
proves that this factoring preserves the original loop's requests and replies.
It is proof support, not an alternative runtime interpreter.

For arbitrary finite fuel, `output_safety` permits either the expected outcome
or interpreter fuel exhaustion. `output_agreement` excludes exhaustion for a
returned worker with sufficient fuel. The main `same_output` additionally proves
that workers return and that the durable completion record contains the outcome.

The earlier exact-Db theorem follows [ReplaySnapshot](ReplaySnapshot.lean),
[SnapshotStep](SnapshotStep.lean), [FairDriver](FairDriver.lean), and
[QueueContract](QueueContract.lean). It shares pure semantics, codecs, and location
laws with the concurrent proof, but treats worker steps as serialized.

## Verification

Run `lake build` and `lake test`. To inspect the main proof dependencies, put this
in a Lean file and run it with `lake env lean`:

```lean
import LeanCloud.Proofs

#print axioms LeanCloud.Proofs.same_output
#print axioms LeanCloud.Proofs.ConcurrentRecovery.same_output
#print axioms LeanCloud.Proofs.ConcurrentAudit.attempts_no_loss
#print axioms LeanCloud.Proofs.ConcurrentRepeated.eventually_returns
```

The equivalence theorems use only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms. They contain no `sorry` or custom assumptions hidden as
axioms; codec, comparison, and fairness requirements are theorem hypotheses.
