# Interpreter tests

Run everything from the repository root:

```sh
lake test
```

The suite lists its named cases with `lake test -- --list`. Some cases also iterate over values,
fuel budgets, journal writes, or queue updates. There are no additional test
dependencies. Any failure prints its test name and exits with a nonzero status.

Use `--` to pass arguments through Lake to the test runner:

```sh
lake test -- --list
lake test -- differential/parallel/
lake test -- generated/seed/42
lake test -- replay/checkpoints/ replay/fuel/
lake test -- queue/
lake test -- recovery/
lake test -- lease/
lake test -- leased-replay/
lake test -- journal/
lake test -- simulation/
lake test -- worker/
```

Filters are test-name prefixes; multiple filters select their union. A filter that
matches nothing fails rather than silently succeeding.

`worker/` checks typed configuration, connection cleanup, durable completion,
restart after acknowledgement failure, and blob connection wiring. Generated
pure programs also compare direct + SimM, replay + SimM, and the IO worker startup
path using the same simulated primitives. These tests do not connect to real
services. The separate [runtime integration suite](../runtime/Integration.lean)
checks generated PostgreSQL tables and database/queue/blob adapters. It also
compares 32 generated pure programs with direct evaluation and simulated replay. Run it together with the
multi-process recovery checks using `lake exe cloud_runtime_tests`.

`lake exe cloud_chaos --seed 1` randomly kills and restarts real workers
running the file example, then requires the correct durable result after crashes
stop. It retains its seeded fault plan and logs. See the
[deployment guide](../LeanCloud/Deployment.md) for scope and options.

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
| [Recovery.lean](Recovery.lean) | Single-worker SimM recovery; interruptions before commit and before reply at every boundary of selected fixtures and 32 generated pure programs; repeated crashes, pauses, retained durable state, and distinct workflow-error and fuel-exhaustion outcomes. |
| [LeaseQueue.lean](LeaseQueue.lean) | Primitive enqueue/dequeue/renew/ack; expiry and redelivery; stale receipts; duplicate payloads; repeated expiry; crashes and lost replies around dequeue, enqueue, renewal, and acknowledgement. |
| [LeasedReplay.lean](LeasedReplay.lean) | The actual replay interpreter over leased transport; interruptions before/after individual Db operations, enqueues, acknowledgement, and final-result publication; duplicate deliveries; explicit lease-time advancement; backend handles and receipts. |
| [JournalDb.lean](JournalDb.lean) | Independent child records; interleaved sibling completions; late fork initialization; duplicate completion; observed conflicts; malformed physical records. |
| [Simulation.lean](Simulation.lean) | Two workers running the actual interpreter; independent commits and response delivery; local state discarded on restart; delayed reads; lease expiry and stale receipts; concurrent sibling completion; completed-ancestor race regression; interruption at every boundary of selected runs; all 256 eight-event scheduling prefixes of a fixture; 96 reproducible workflow/schedule/crash combinations compared with direct evaluation. |
| [ConcurrentJournal.lean](ConcurrentJournal.lean) | Actual `putSame` and full `put` calls; delayed absent-key responses; complementary partial arrays; all 256 eight-event scheduling prefixes; crashes at every boundary of a three-record publication; 16 repeated-crash schedules; late initialization after completed publication; empty groups, duplicate completion, malformed inputs, and a same-key disagreement counterexample. |
| [ConcurrentRead.lean](ConcurrentRead.lean) | Actual readers overlapping actual publishers; delayed cached and missing replies; a mixed view that never existed as an atomic snapshot; retention of pre-existing slots; crashes at all ten boundaries of a three-child read; all 256 eight-event scheduling prefixes; empty groups; 32 reproducible schedules with and without repeated crashes. |
| [ConcurrentJoin.lean](ConcurrentJoin.lean) | Two actual `finish` calls; sibling success and failure priority; nested parents and duplicate completion; crashes at every first-worker boundary while the other finishes; root completion and reuse of a completed child group without its own cache; a lost last-slot reply without a result cache; all 1,024 ten-event scheduling prefixes; 32 reproducible schedules with and without repeated crashes. |
| [ConcurrentPublication.lean](ConcurrentPublication.lean) | Actual queue publication requests; overlapping and duplicate requests, stale receipts, partial and empty successor lists, final-result publication; coverage checked at each scheduled boundary; all enabled scheduling prefixes up to ten events; crashes at every first-publisher boundary; a conflicting-plan counterexample; full interpreter recovery before/after parent enqueue, child acknowledgement, and final-result publication; delayed empty replies after parent consumption; changed replies on retry. |

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

## External crash and restart

[Recovery.lean](Recovery.lean) runs the actual interpreter over
[`SimulationBackend`](../LeanCloud/SimulationBackend.lean). Recovery and concurrent
execution share `SimM`; crashes are external scheduling events.

A worker first waits to commit an atomic operation, then waits to receive its
saved response. The boundary sweep enumerates both states for every operation of
an uninterrupted run. At each boundary it crashes the worker, checks that durable
state is unchanged, explicitly advances lease time, and restarts a fresh attempt.
The returned result and durable completion record must match direct evaluation.
This includes individual journal reads/writes, enqueues, and acknowledgements.

[SimulationSupport.lean](SimulationSupport.lean) supplies the one-worker test
driver. [Simulation.lean](Simulation.lean) supplies two-worker scheduling and
interleaving tests. Both use the same external events. A finite event list can
leave a worker paused; a test driver's event budget is separate from interpreter
fuel and from workflow errors. Tests also cover lost replies from exec without
turning the crash into a journaled `CloudError`.

## Lease primitives

[LeaseQueue.lean](LeaseQueue.lean) tests the pure
[lease model](../LeanCloud/LeaseQueueModel.lean), including operations wrapped with
`SimM.atomic` and interrupted by explicit simulation events. Each enqueued message has its
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
outcome survive in the simulator's durable state. Db and blob wrappers thread
the backend handle without disturbing the receipt. The Db wrapper uses
[JournalDb](../LeanCloud/JournalDb.lean), so the boundary sweeps include its
individual physical reads and writes.

For runnable work, the adapter enqueues each successor separately and then
acknowledges the current receipt. For completion, it writes the run's final result
to the Db before acknowledgement. The backend supplies typed callbacks to read
and persist that result. A restart can therefore return an already saved outcome
even if the final message was never acknowledged; draining such leftover messages
is separate cleanup work.

The recovery sweeps explicitly advance time after interruption so the old lease
expires before the worker resumes. Crash and restart themselves leave the clock
unchanged. The distinct 32 generated pure workflows are swept once through this
shared backend. Additional leased tests insert duplicate publications, interrupt
between successor enqueues and between final-result publication and acknowledgement,
and reject stale receipts without removing newer deliveries.

[ConcurrentHandoff.lean](../LeanCloud/Proofs/ConcurrentHandoff.lean) and
[ConcurrentAudit.lean](../LeanCloud/Proofs/ConcurrentAudit.lean) prove publication
before acknowledgement, including overlapping processing and stale receipts.
The main [concurrent equivalence theorem](../LeanCloud/Proofs/ConcurrentEquivalence.lean)
proves both returned and durable outcomes under its explicit fairness conditions.

The concurrent publication tests check that every incoming item remains queued
until its supplied replacement work is durable. The corresponding batch proof
assumes agreement between requests sharing a slot and leaves new successors for
later consumers. A deliberately conflicting pair of requests demonstrates why
the agreement premise matters. Separate full-interpreter tests restart with a
fresh receipt after crashes on both sides of the three handoff boundaries above;
these exercise recovery beyond the current batch theorem. Additional regressions
let another worker consume the parent before an old empty reply acknowledges,
and crash a child whose retry now enqueues the completed parent instead of
returning no work. The changed reply is interrupted before and after its enqueue.

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

The [storage proofs](../LeanCloud/Proofs/README.md) establish reconstruction and
preservation of compatible records under arbitrary legal simulation schedules,
including partial publication, delayed replies, crashes, and retries. Concurrent
read observations are bounded by the journal before and after the read; they need
not be a simultaneous snapshot. Agreement and comparison laws remain explicit.
These properties support the full pure-workflow equivalence theorem.

A mixed-read regression pauses a reader after observing child 0 absent. The writer
then commits child 0 and child 1 in order. When resumed, the reader sees child 1
present and returns a partial array that never existed as a simultaneous storage
state. A fresh read sees both results and completes. Tests also restart a reader
at every physical read/reply boundary after allowing the publisher to finish;
the restarted read must include all the newly durable children.

Join tests run the actual child-completion code and require both durable child
records, the expected group result, and at least one parent wakeup request.
They also check recovery after committing the last slot but losing its reply:
the retry recognizes completion from child records alone, without a cached group
result. These focused tests stop at the wakeup request; they do not enqueue it.
The concurrent completion proof now covers the full `finish` call under its
explicit storage assumptions, including arbitrary finite crash/restart schedules.
The [wakeup theorem](../LeanCloud/Proofs/ConcurrentWakeup.lean) additionally proves
that returned attempts for all children of a nonempty group cannot all omit the
parent notification. The simulated raw Db retains a write log to order reread
points; clients continue to use the same atomic key/value interface.

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

The core suite exercises simulated interleaving on one thread and ideal in-memory
storage. Lease primitives and replay cover redelivery and duplicate messages
with serialized attempts and with interleaved simulated workers. The separate
container suite tests real concurrent workers and service adapters. Hosted cloud
deployments and cancellation are not tested.
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
and real adapters are outside its scope. The concurrent equivalence theorem separately covers pure workflows with
crashes and interleaved workers. The tests also exercise runtime effects.

[Queue laws](../LeanCloud/Proofs/WorkQueue.lean) specify valid selection, retention,
completion reporting, and weak fairness. Finite tests check representative
schedules; they do not prove backend fairness.
