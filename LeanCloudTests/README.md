# Tests

```sh
lake test
lake exe lean_cloud_tests --list
lake exe lean_cloud_tests generated/chaos
lake exe lean_cloud_tests crash/
lake exe lean_cloud_tests sequential/
lake exe cloud_runtime_tests
lake exe cloud_chaos --seed 1
```

The generator produces finite Cloud programs containing values, recorded pure
computations, blobs, delays, failures, captured inputs, dependent binds, and nested
parallel groups, including empty groups. Every generated program runs through the
direct interpreter and through the same scheduler/worker actors used in deployment.
The comparison checks the durable final value or error and completed-branch replay.
Generated parallel results use an order-sensitive fold. Targeted cases complete
children in reverse order and check source-ordered values and errors after all
children finish.

The pure sequential driver is also compared directly against direct evaluation:
256 generated programs plus targeted cases for nested and empty groups,
captured inputs, delays, typed results, ordered errors, and insufficient fuel.
These tests start with empty records, check the durable root, and replay the
completed run with a minimal budget to check cache reuse.

Sim tests include 256 generated programs with and without faults, small exhaustive
compositions, and targeted before/after crash boundaries, including worker receives.
Faults affect the scheduler as well as workers. Uncommitted requests may be lost
or commit after a crash; messages may be
delayed, duplicated, or redelivered after a consumer crash. Confirmed messages
cannot be dropped from the model. After faults stop, the driver continues timers and
fair scheduling. On completion it commits remaining orphan requests and checks
that existing records survive unchanged; every scheduled branch must be done.
Error messages retain the generation seed and program tree.

Protocol tests check repeated assignment requests, duplicate and stale reports,
empty and partial joins, immutable record creation, JSON codecs, and the different
lifetimes of local database operations and remote requests.
Nested-child replay also runs with a store that rejects ancestor-join reads:
descending into a child must not depend on those records.
Replay tests reject missing prefixes, premature joins, changed requests, malformed
values, and invalid locations without writing records. They count actual `exec`
calls across reconstruction and repeated assignments, check that a losing writer
uses the canonical result, and distinguish IO failures from durable workflow
errors. Codec round trips serialize and parse JSON text. Blob cases cover missing
names, integrity errors, and invalid UTF-8, with and without simulated crashes.

The test build also checks [ProofExamples.lean](ProofExamples.lean), which applies
all three public equivalence theorems to the same nested parallel workflow, and
[ProgressWitness.lean](ProgressWitness.lean), which proves that an actual run
from empty storage satisfies the completion theorem's processing-window premise.
Its scheduler updates its private database while the worker is between replay
operations, so the witness also checks interference inside a processing window.

Real adapter properties compare 16 generated programs using independent RabbitMQ
brokers, SQLite, and S3 with
direct evaluation. Concurrent blob writers must receive the same canonical record;
invalid blob references, missing names, and invalid UTF-8 must be rejected. Mailbox tests
close consumers without acknowledging and verify 24 successive redeliveries on
every broker. Identically named queues on different brokers must retain different
payloads; unknown worker routes and duplicate configured identities are rejected.
After acknowledgement, a new consumer must receive the next confirmed message
instead of the old delivery; an empty poll on the original consumer is insufficient.
A SIGKILL of each broker immediately after creating
a mailbox and confirming its first publication must preserve that message.
While that broker is down, another must still accept and deliver messages.
Container tests exercise actual mailbox transport, multiple worker processes, and
restarts. Chaos plans are generated before execution and recorded with logs; the
seed reproduces the plan, not OS timing.

Console tests cover pause/resume and permanent kill, including interrupted
commands, restart policies, and isolation between runs. Real runtime tests check
that typed process handles observe cancellation, repeated cancellation preserves
the same root record, and a completed result cannot be overwritten by kill.

Arbitrary interacting IO effects need not commute. Differential cases use pure
computations and immutable blob operations; they do not claim that scheduling
preserves the behavior of all user-provided IO actions.
