# Interpreter tests

Run everything from the repository root:

```sh
lake test
```

The suite currently contains 610 named cases. Some cases also iterate over values,
fuel budgets, journal writes, or queue updates. There are no additional test
dependencies. Any failure prints its test name and exits with a nonzero status.

Use `--` to pass arguments through Lake to the test runner:

```sh
lake test -- --list
lake test -- differential/parallel/
lake test -- generated/seed/42
lake test -- replay/checkpoints/ replay/fuel/
lake test -- queue/
lake test -- crash/
lake test -- lease/
lake test -- leased-replay/
lake test -- journal/
```

Filters are test-name prefixes; multiple filters select their union. A filter that
matches nothing fails rather than silently succeeding.

## What the comparison checks

[Support.lean](Support.lean) runs the same `Cloud` program against two fresh copies
of the same model backend. `DirectInterpreter.interpret` supplies the expected
behavior through structural recursion, without fuel or a scheduling policy.
Replay receives enough fuel and a model queue that selects pending locations in
numeric path order. That policy reproduces the direct interpreter's array order.

Each differential case compares:

1. The final value, or the complete typed `CloudError`.
2. The ordered primitive-effect trace, including arguments and execution counts.
3. Blob contents, names, and allocation state.
4. A second run with the retained queue and journal: the outcome must be the same, with no
   new primitive effects or changes to recorded outcomes.

The journal is interpreter bookkeeping, so its contents are not compared with the
direct interpreter. Instead, the tests require the direct interpreter to make no
journal reads or writes. Blob allocation uses fresh keys to make duplicate writes
observable.

Each replay step advances one primitive effect, fork, join, or completion.
Other queue policies can interleave effects across branches, including nested groups.
Both interpreters
run every child even after a typed failure, and then select the first failure in
array order. Result order is also independent of completion order. Known-result
and known-effect-order assertions check the oracle as well: agreement alone could
miss a bug in shared primitive execution.

[WorkQueue.lean](WorkQueue.lean) tests replay with first, last, scripted, and
reproducible pseudorandom selection policies implemented by the environment.
Explicit scripts check interleaved effect order. Generated programs with
schedule-independent results are compared with direct evaluation under three
policies; their effect multisets must match after normalizing blob allocation
order. A shared-counter example deliberately produces different results under
different policies: arbitrary schedules need not agree with sequential execution.
A completed environment must return its final outcome without selecting more work.

## Coverage

| Module | Checks |
| --- | --- |
| [Pure.lean](Pure.lean) | Recorded pure calculations, captured inputs, dependent binds, parallel pairs, blob inputs, cached values, and the Id backend. |
| [Differential.lean](Differential.lean) | Pure values, delays, mixed result types, captured values, data-dependent control flow, heterogeneous `\|\|`, empty/single/wide/nested/successive parallel groups, continuation chains, failure order, blob operations and errors. |
| [Generated.lean](Generated.lean) | 256 reproducible generated programs combining binds, branches, delays, effects, blobs, failures, and parallel groups; all 32 ordered two-leaf compositions under bind and parallel. |
| [Replay.lean](Replay.lean) | Restart after every journal write in selected workflows, fuel exhaustion, cached results and failures, rejected writes, malformed records, and selected divergence checks. |
| [Codecs.lean](Codecs.lean) | Codec round trips, malformed input rejection, binary data, journal records, and an explicit broken-codec counterexample. |
| [Backends.lean](Backends.lean) | Separate Db and blob interfaces over `Id` and `IO`, returned backend handles, state-dependent effect results, native exceptions, deep parallel nesting, and location navigation. |
| [WorkQueue.lean](WorkQueue.lean) | Scripted interleaving; state-dependent results; nested pending work; error and result ordering; heterogeneous pairs; empty groups; numeric location order; 128 generated programs under three policies; restart under a different schedule; interruptions around every queue update; temporary idle responses. |
| [Crash.lean](Crash.lean) | Pure crash model; interruptions before/after every Db and queue primitive in selected fixtures and 32 generated pure programs; automatic retry and changed scheduling; repeated crashes; retained durable state; discarded worker-local state; separate crash, workflow-error, and fuel-exhaustion outcomes. |
| [LeaseQueue.lean](LeaseQueue.lean) | Primitive enqueue/dequeue/renew/ack; expiry and redelivery; stale receipts; duplicate payloads; repeated expiry; crashes and lost replies around dequeue, enqueue, renewal, and acknowledgement. |
| [LeasedReplay.lean](LeasedReplay.lean) | The actual replay interpreter over leased transport; interruptions before/after individual Db operations, enqueues, acknowledgement, and final-result publication; duplicate deliveries; repeated crashes; 16 generated workflows; backend handles and receipts. |
| [JournalDb.lean](JournalDb.lean) | Independent child records; interleaved sibling completions; late fork initialization; duplicate completion; observed conflicts; malformed physical records. |

Generated failures print both the seed and the program tree. The generator uses
fixed seeds, so the same test can be rerun with a prefix such as
`generated/seed/42`.

## Recovery boundaries

The checkpoint tests first obtain an uninterrupted baseline. For each journal
write in that run, they start again from an empty journal and inject an exception
immediately after that write commits. They discard the interrupted interpreter
call and restart using the retained queue and backend state. The recovered outcome, effect
trace, backend state, and final journal must match the baseline. The workflows
include nested groups, blobs, typed failures, and an empty group.

Fuel tests repeat this comparison for initial budgets 0 through 79, then resume
with enough fuel to complete.

Queue recovery tests also interrupt every journal write, including the gap
between completing a child and updating its parent's slot. They resume with a
different pseudorandom schedule. These fixtures use schedule-independent results
and unique effect labels: the output and final journal must match, and the effect
multiset must be unchanged even if execution order differs. In general, changing
the schedule can change results when effects share mutable state.

Queue-update tests interrupt immediately before and after every atomic publication
of successor locations or the final outcome. Restart must retain pending work and
avoid repeating committed effects. An idle response is not treated as completion;
an environment with no work is never silently reseeded by the interpreter.

An effect can execute before its outcome is committed. A separate test interrupts
that gap and checks that replay executes it again. This suite therefore does not
claim exactly-once external effects across that boundary.

Native `IO` exceptions escape both interpreters and stop the current execution.
They differ from typed cloud failures, whose outcomes are collected and recorded.

## Explicit crash model

[Crash.lean](Crash.lean) also runs the existing interpreter in
`CrashM`, an exception layer over durable state. Unlike the IO injection tests,
this is a pure, inspectable model. The fault script is separate harness bookkeeping;
each primitive consumes one entry and either crashes before committing, crashes
after committing, or returns normally. Neither crashes nor retries reset the
script or durable state.

The outer runner takes a fresh worker-local state on every attempt:

```lean
let attempt := Prod.fst <$> (interpret db blobs queue fuel program input).run ()
let (result, state) := (CrashM.restart 3 attempt).run initial
```

Here `3` permits three retries after the first attempt. The result has type
`Except Crash (Except CloudError α)`: retry exhaustion remains a crash; workflow
errors and interpreter fuel exhaustion return normally through the inner layer.
The caller initializes the Db and root item once, outside the runner.

Boundary sweeps compare direct evaluation with both automatic retry and explicit
restart under the opposite queue policy. They use ordinary pure values, delay,
failure, and parallel; a separate exec test checks that a crash bypasses the
interpreter's CloudError handler without being journaled as a failure.

The tests above retain selected work until an atomic `complete` operation. The
leased replay tests below separate successor publication and acknowledgement;
they do not assume that stronger atomic queue contract.

## Lease primitives

[LeaseQueue.lean](LeaseQueue.lean) tests the pure
[lease model](../LeanCloud/LeaseQueueModel.lean), including operations wrapped with
`CrashModel.atomic` and retried by the outer runner. Each enqueued message has its
own slot, even when the payload is an identical `Location`. Dequeue retains the
message and returns a receipt; acknowledgement uses the receipt, not the payload.

Time advances only through `advance`. Before expiry, a leased message is hidden
from dequeue; at expiry it is eligible again. Redelivery and renewal return a new
receipt, invalidating earlier receipts. Expiry alone permits redelivery but does
not invalidate the current receipt if nobody has acquired the message again.
The tests check exact expiry, lost renewal replies, and 100 successive deliveries.

A crash after dequeue leaves the message leased. An immediate restart can find
no visible work; it neither releases the lease nor silently advances time. A
crash before acknowledgement leaves work recoverable; after acknowledgement,
the message is gone. Retrying enqueue after losing its reply creates a duplicate.

This is an ideal queue, with strict validation of current receipts and no
unsolicited duplicate delivery during a lease. It is not a contract already
proved for Azure or AWS. The receipt rotation follows
[Azure's dequeue](https://learn.microsoft.com/en-us/rest/api/storageservices/get-messages)
and [renewal](https://learn.microsoft.com/en-us/rest/api/storageservices/update-message)
behavior. [SQS standard queues](https://docs.aws.amazon.com/AWSSimpleQueueService/latest/SQSDeveloperGuide/sqs-visibility-timeout.html)
can deliver duplicates even within the visibility timeout. A real adapter and
concurrent replay must account for the service's guarantees.

## Replay with leased deliveries

[LeasedReplay.lean](LeasedReplay.lean) supplies the existing interpreter with
[LeaseQueue.toWorkQueue](../LeanCloud/LeaseQueue.lean). The adapter keeps the
current receipt in worker-local state, while Db records, messages, and the final
outcome survive in the crash model's durable state. Db and blob wrappers thread
the backend handle without disturbing the receipt. The Db wrapper uses
[JournalDb](../LeanCloud/JournalDb.lean), so the boundary sweeps include its
individual physical reads and writes.

For runnable work, the adapter enqueues each successor separately and then
acknowledges the current receipt. For completion, it writes the run's final result
to the Db before acknowledgement. The backend supplies typed callbacks to read
and persist that result. A restart can therefore return an already saved outcome
even if the final message was never acknowledged; draining such leftover messages
is separate cleanup work.

The test environment explicitly advances time by one unit before each transport
poll, so a crashed worker's three-unit lease can expire during later polls.
Catching the crash itself does not release the lease. Boundary sweeps interrupt
every primitive in selected workflows and 16 generated programs, restart with a
fresh worker, and compare against direct evaluation. Other cases insert duplicate
messages, interrupt between two successor enqueues, and reject a stale receipt
without removing the newer delivery.

[LeasePublication.lean](../LeanCloud/Proofs/LeasePublication.lean) also proves the
adapter's publication ordering with separately atomic primitives: either the
incoming delivery survives, or its successors (or final result) are durable.
The proofs include stale receipts, invalid completion calls, and reading an
already saved final result without dequeuing leftover work.

These recovery runs serialize worker attempts. The journal tests below separately
exercise controlled overlapping completions. The existing `same_output` theorem
still assumes the ideal logical Db and atomic queue contract; equivalence across
physical storage, leased delivery, concurrent workers, and crashes remains to be
proved.

## Independent child records

All workers of a run use `JournalDb.ofDb` over the same run-scoped raw Db. A group
at `0:0` uses separate physical keys:

```text
0:0/fork       -- immutable child count
0:0/child/0    -- first child's outcome
0:0/child/1    -- second child's outcome
0:0/result     -- completed outcome, when cached
```

`Result.suspended` remains the interpreter's logical view; this adapter assembles
it from the child records rather than storing a shared mutable array. Publishing
a partial view writes only present slots. Missing slots never erase records.
The last child's slot is persisted before any completed-group cache.

After publishing a child outcome, `finish` rereads the group. If two workers both
started with incomplete views, the worker that sees the complete group publishes
the parent as runnable. The tests pause one worker before its child write, run
the other worker's actual `finish`, then resume the first; both orders preserve
both outcomes and wake the parent. Another interleaving delays fork initialization
until after the group completes and checks that the completed result survives.

Individual raw reads and writes are atomic. Concurrent writers to the same key
must agree on its value, as they do for stable pure workflows. The adapter rejects
observed disagreements, but its read/check/write is not compare-and-set and cannot
resolve simultaneous conflicting values. These tests do not establish exactly-once
external effects or full concurrent replay correctness.

The [storage proofs](../LeanCloud/Proofs/README.md) now establish read
reconstruction and preservation of compatible records across interrupted
publication. They also derive eventual publication with enough retries for any
finite fault script. These proofs cover serialized attempts and explicitly state
the agreement and JSON comparison assumptions; the interleaving tests exercise
behavior beyond that proof scope.

## Adding a case

Use `expect` for a program with a known result. It also runs the full differential
comparison and the second replay:

```lean
expect "parallel/captured-input" (fun ref => cloud {
  let n ← execValue ref "input" 4
  Cloud.parallel #[pure (n + 1), execValue ref "right" (n * 2)]
}) (.ok #[5, 8])
```

Use `checkpointSweep program` to restart after every committed journal write, or
`fuelSweep program` to test interrupted prefixes. New case collections must be
included in `allCases` in [LeanCloudTests.lean](../LeanCloudTests.lean).

## Scope

These tests exercise simulated interleaving on one thread and ideal in-memory
storage. Lease primitives and replay cover redelivery and duplicate messages
with serialized attempts. Concurrent leased workers, database adapters, cloud
deployments, and cancellation are not tested.
Choice has only an explicit unsupported-operation check.

Differential comparison assumes the queue selects the sequential reference order,
enough replay fuel, stable program/input, and codecs that round-trip persisted values.
The direct interpreter does not serialize
values, so a broken codec can make replay fail while direct execution succeeds;
the suite demonstrates that distinction.

The separate [equivalence theorem](../LeanCloud/Proofs/QueueContract.lean) proves
equal results/errors for pure `Cloud Id` programs containing ordinary pure values,
delay, failure, and parallel. It uses an ideal Db and a lawful fair queue, permits
arbitrary pending-item selection, and derives sufficient fuel. It has no external
user state or effect-order assumptions.

The theorem covers fresh runs with serialized worker steps. Exec (including the
recorded `Cloud.pure` helper), blobs, restart correctness, simultaneous workers,
and real adapters are outside its scope. The tests above still exercise these
runtime effects and modeled recovery scenarios.

[Queue laws](../LeanCloud/Proofs/WorkQueue.lean) specify valid selection, retention,
completion reporting, and weak fairness. Finite tests check representative
schedules; they do not prove backend fairness.
