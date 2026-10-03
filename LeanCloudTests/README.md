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
Parallel failures are selected in source order after all children finish.

The pure sequential driver is also compared directly against direct evaluation:
256 generated programs plus targeted cases for nested and empty groups,
captured inputs, delays, typed results, ordered errors, and insufficient fuel.
These tests start with empty records, check the durable root, and replay the
completed run with a minimal budget to check cache reuse.

Sim tests include 256 generated programs with and without faults, small exhaustive
compositions, and targeted before/after crash boundaries. Faults affect the
scheduler as well as workers. Requests may commit after a crash; messages may be
delayed, duplicated, or redelivered after a consumer crash. Confirmed messages
cannot be dropped from the model. After faults stop, the driver continues timers and
fair scheduling. Error messages retain the generation seed and program tree.

Protocol tests check repeated assignment requests, duplicate and stale reports,
empty and partial joins, immutable record creation, JSON codecs, and the different
lifetimes of local database operations and remote requests.

The test build also checks [ProofExamples.lean](ProofExamples.lean), which applies
all three public equivalence theorems to the same nested parallel workflow, and
[ProgressWitness.lean](ProgressWitness.lean), which proves that an actual run
from empty storage satisfies the completion theorem's processing-window premise.
Its scheduler updates its private database while the worker is between replay
operations, so the witness also checks interference inside a processing window.

Real adapter properties compare 16 generated programs using RabbitMQ, SQLite, and S3 with
direct evaluation. Concurrent blob writers must receive the same canonical record. Mailbox tests
close consumers without acknowledging, verify 24 successive redeliveries, and
check removal after acknowledgement. A broker SIGKILL immediately after creating
a mailbox and confirming its first publication must preserve that message.
Container tests exercise actual mailbox transport, multiple worker processes, and
restarts. Chaos plans are generated before execution and recorded with logs; the
seed reproduces the plan, not OS timing.

Arbitrary interacting IO effects need not commute. Differential cases use pure
computations and immutable blob operations; they do not claim that scheduling
preserves the behavior of all user-provided IO actions.
