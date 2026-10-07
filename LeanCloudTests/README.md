# Tests

```sh
lake test
lake exe lean_cloud_tests --list
lake exe lean_cloud_tests generated/chaos
lake exe lean_cloud_tests crash/
lake exe lean_cloud_tests sequential/
lake exe lean_cloud_tests pool
(cd runtime && lake exe cloud_inbox_tests)
lake exe cloud_console_tests
lake exe cloud_console_tests --pool-only
lake exe cloud_console_tests --scaling-only
lake exe cloud_console_tests --chaos-only --seed 1
lake exe cloud_runtime_tests
lake exe cloud_chaos --seed 1
```

CI runs the real pool recovery, scaling, and generated chaos suites in separate
Docker jobs on pull requests and pushes to `main`. A failed suite does not cancel
the others.
Failures retain build/startup output, the test transcript, and available scheduler,
worker, and blob-service logs and health state for seven days. Test containers and
volumes are isolated from the user's deployment and cleaned up after each suite.

CI caches the pinned Lean toolchain and Lake build outputs. Proof checks and tests
still run on every commit. Docker image preparation is a separate timed step,
using persistent BuildKit caches for the demo and generated chaos application.
Dependencies are compiled in image layers so they survive cache export and source
changes. Each suite then uses that same builder for its ordinary `deploy` calls;
deployment, compilation checks, and recovery assertions are still exercised.
An empty cache performs the complete build, and cache export failures do not hide
test failures. The first run populating these caches will still take longer.

`--chaos-only` deploys a test application on the production shared pool: three
workers, one scheduler, and S3-compatible blob storage. Three generated pure
workflows run together, with nested parallel groups, captured inputs, dependent
binds, and competing failures. Six seeded faults kill and restart active scheduler
or worker nodes, with later faults waiting for completed branches. After faults
stop, every durable result must equal direct evaluation, including the selected
error. A final scheduler restart checks that
completed outcomes survive. No timing effects or interpreter hooks are added to
the workflows. The test fails if it cannot find active work to exercise.

The retained test directory contains `chaos-plan.json` with inputs, program trees,
expected outcomes, and the fault plan, plus `chaos-events.jsonl` with observed
assignments, actual victims, restart evidence, and results. CI retains these on
failure along with node logs. `--seed N` reproduces generated programs and fault
choices; concurrent timing and the set of busy workers may differ.

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

Shared-pool tests run three generated workflows on three workers, using the
actual `Worker.execute` interpreter and `Sim` to interleave record operations.
Across 64 seeds, each trace starts with real parallel suspensions, then performs
400 operations mixing progress, pause/resume/kill, worker membership changes,
assignment expiry and renewal, restarts, delayed/duplicate reports, and orphaned
writes. Checks after each transition cover run isolation, attempt ownership,
immutable records, and agreement with direct evaluation. Surviving workflows
must finish once faults stop. Scheduler transitions are atomic in these tests;
HTTP delivery and SQLite durability are checked separately by the adapter tests.
Targeted failure cases exhaust the actual replay interpreter's fuel inside a
parallel child, then check sibling revocation, stale reports, restart, terminal
controls, and continued use of shared workers by another run.

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

Inbox properties compare real SQLite with `MailboxModel` over 32 generated traces
of 200 operations. They also check SIGKILL recovery, termination signals, HTTP
authentication, lease expiry and renewal, and rejection of stale consumers.
The native suite also runs the real Pool scheduler over HTTP and SQLite: busy
work retains its assignment, pause revokes it, failed computations stop renewing,
and stale heartbeats cannot renew replacement attempts.

Real adapter properties compare 16 generated programs using HTTP/SQLite inboxes,
private scheduler SQLite, and S3 with direct evaluation.
They also run the real Pool scheduler from durable snapshots before and after
failure publication, preserve an earlier root result, and exercise a live child
failure through the worker interpreter, typed process handles, and application
API. Duplicate/late reports and kill must preserve the failure; an IO exception
must remain retryable and another run must still complete on the same worker.
Concurrent blob writers must receive the same canonical record;
invalid blob references, missing names, and invalid UTF-8 must be rejected. Mailbox tests
close consumers without acknowledging and verify 24 successive redeliveries on
every inbox service. Identically named queues on different inbox services must retain different
payloads; unknown worker routes and duplicate configured identities are rejected.
After acknowledgement, a new consumer must receive the next confirmed message
instead of the old delivery; an empty poll on the original consumer is insufficient.
A SIGKILL of each inbox service immediately after creating
a mailbox and confirming its first publication must preserve that message.
While that inbox service is down, another must still accept and deliver messages.
Container tests exercise actual mailbox transport, multiple worker processes, and
restarts. Chaos plans are generated before execution and recorded with logs; the
seed reproduces the plan, not OS timing.

Console tests cover pause/resume and permanent kill, including interrupted
commands, restart policies, and isolation between runs. Real runtime tests check
that a 35-second computation completes once despite the default 30-second
assignment lease. They also check
that typed process handles observe cancellation, repeated cancellation preserves
the same root record, and a completed result cannot be overwritten by kill.

Arbitrary interacting IO effects need not commute. Differential cases use pure
computations and immutable blob operations; they do not claim that scheduling
preserves the behavior of all user-provided IO actions.
