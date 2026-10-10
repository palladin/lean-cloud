# Tests

Size-controlled stress checks run with the normal model suite. The larger
benchmark compares Direct, SequentialReplay, ParallelReplay and restarting
parallel replay for 1,024 children, 48 nested forks and 4,096 recorded commands.
Every branch is interrupted before a read and after its committed return. A
32-run Pool workload also interleaves faults and administration on three workers.

```sh
lake exe cloud_stress_tests
lake exe cloud_console_tests --stress-only
```

The first command emits JSON measurements: elapsed milliseconds, record counts,
reads, creates and exercised crashes. CI saves these alongside `/usr/bin/time -v`
peak process memory/CPU measurements. On macOS, use `/usr/bin/time -l` instead.
Timings are observations, not pass/fail thresholds; zero milliseconds means less
than the clock's resolution. These pure journal timings do not predict network
throughput. The second command runs 15 workflows through the actual HTTP/SQLite/S3
deployment, compares all outcomes with Direct, saves `stress-results.json` under
its isolated deployment directory, and removes its containers afterward. It is
opt-in so the ordinary CI recovery suites keep their time budget.

```sh
lake test
lake exe lean_cloud_tests --list
lake exe lean_cloud_tests generated/chaos
lake exe lean_cloud_tests crash/
lake exe lean_cloud_tests replay-drivers/
lake exe lean_cloud_tests restarting-replay/
lake exe lean_cloud_tests pool
(cd runtime && lake exe cloud_inbox_tests)
lake exe cloud_console_tests
lake exe cloud_console_tests --pool-only
lake exe cloud_console_tests --scaling-only
lake exe cloud_console_tests --chaos-only --seed 1
docker compose run --build --rm checks
```

CI runs library/proof checks on pull requests and pushes to `main`, then passes
the compiled CLI and test driver to the Docker job. Both jobs use Ubuntu 24.04;
the Docker job uses the runner's libcurl runtime and installs no native development
packages or Lean toolchain. Docker Bake builds the demo and generated chaos images
together, sharing identical toolchain setup steps. CLI lifecycle, pool recovery,
scaling, and generated chaos use that same builder. The four suites run concurrently
on isolated deployments, using the already-built test driver. The runner waits for
every suite and fails if any suite fails; one failure does not cancel the others.
Both CI jobs have a fifteen-minute execution limit, allowing headroom above the
usual 7–10 minute full-run target. Runtime suites have six-minute limits except
network/crash chaos, which has eight minutes to outlast real assignment leases.
A timeout fails the check rather than omitting tests.
Failures retain build/startup output, the test transcript, and available scheduler,
worker, and blob-service logs and health state for seven days. Test containers and
volumes are isolated from the user's deployment and cleaned up after each suite.

Native setup installs only missing packages. It first uses the runner's package
indexes; failed downloads retry with fresh, signed indexes from Ubuntu's official
archive. Download, refresh, and offline installation have separate limits within
the five-minute setup budget. CI checks timeout recovery and failure propagation
without touching system packages.
CI caches the pinned Lean toolchain and Lake build outputs. Proof checks and tests
still run on every commit. Docker image preparation is a separate timed step,
using persistent BuildKit caches for the demo and generated chaos application.
Dependencies are compiled in image layers so they survive cache export and source
changes. CI files are excluded from the Docker context. Image preparation fills
the build cache without loading unused images into Docker. Each suite then uses
that same builder for its ordinary `deploy` calls;
deployment, compilation checks, and recovery assertions are still exercised.
Docker layers use fast zstd compression and one Actions cache archive, avoiding
separate uploads for each layer. Existing GitHub BuildKit caches remain a fallback
with a 30-second request limit. Each image exports its cache during the build.
Completed exports replace old directories only after an index is written,
avoiding cache growth. Shared toolchain blobs are hard-linked so the archive stores
them once. An explicit one-minute cache save runs before the tests,
so later test failures or timeouts do not discard completed image caches. Cache
save failures do not fail the job or hide test failures. No runtime suite is
omitted from a successful run; both images must build before the suites start.
An empty cache still performs the complete build. A cold build or infrastructure
stall may hit the job limit; that is a failed run, not a passing run
with omitted tests. Queueing for a GitHub runner is outside the execution limit.

`--chaos-only` deploys a test application on the production shared pool: three
workers, one scheduler, and S3-compatible blob storage. Three generated pure
workflows run together, with nested parallel groups, captured inputs, dependent
binds, and competing failures. First, it snapshots every replay record already
confirmed by the scheduler for those runs, then disconnects shared blob storage.
Every worker must report a new S3 transport failure, while coordination must
remain free of terminal errors. After at least five seconds of isolation, storage
reconnects. The suite requires fresh branch completions without manual worker or
scheduler restarts, and compares the saved records with their original values.
A test-only command reads them through the production S3 adapter; it never runs
a workflow or opens coordination databases and is not exposed by the HTTP API.

Next, Docker disconnects a busy worker from the deployment network. After expiry,
the affected run must have no replacement assignments while that worker remains
isolated: timeout does not prove it stopped. Synthetic late failure reports and
a heartbeat pass through the real HTTP/SQLite inbox; neither may fail the run
or revive that attempt. The worker reconnects with its original DNS alias,
acknowledges cancellation, and the test requires a fresh root assignment and
further progress. Next, the scheduler loses its
network connection for longer than the configured assignment lease. No explicit
node restart accompanies these network faults; transport errors may trigger the
normal Docker restart policy. All three partitions must recover automatically.

Six seeded faults then kill and restart active scheduler
or worker nodes, with later faults waiting for completed branches. After faults
stop, every durable result must equal direct evaluation, including the selected
error. Duplicate late reports and a final scheduler restart check that
completed outcomes survive. The pre-outage replay records must still match at
the end of the suite. No timing effects or interpreter hooks are added to
the workflows. The test fails if it cannot find active work to exercise.

The retained test directory contains `chaos-plan.json` with inputs, program trees,
expected outcomes, and the fault plan, plus `chaos-events.jsonl` with observed
assignments, network disconnections/reconnections, stop barriers and root reconstruction,
late-message checks, storage failures, actual victims, restart evidence, and
results. `chaos-records-before.json`, `chaos-records-recovery.json`, and
`chaos-records-completion.json` retain the compared record sets. Scheduler
observations establish that root reconstruction happened even if a short assignment
finishes between polls; missing evidence fails the test. Durable results remain
the correctness oracle. CI retains these on
failure along with node logs. `--seed N` reproduces generated programs and fault
choices; concurrent timing and the set of busy workers may differ.

The generator produces finite Cloud programs containing values, recorded pure
computations, blobs, delays, failures, captured inputs, dependent binds, and nested
parallel groups, including empty groups. Every generated program runs through the
direct interpreter and through the shared scheduler transitions and replay worker
under simulation. The deployed pool adds multi-run routing and ownership checks.
The comparison checks the durable final value or error and completed-branch replay.
Generated parallel results use an order-sensitive fold. Targeted cases complete
children in reverse order and check source-ordered values and errors after all
children finish.

The pure sequential and `Task.spawn` parallel drivers are compared with direct
evaluation over the same 256 generated programs. Targeted cases cover nested and
empty groups, captured inputs, typed results, source-ordered errors, insufficient
fuel, and resuming a partially recorded run. Tests compare every journal lookup,
check root results, and replay completed runs with a minimal budget. Additional
checks establish that workers return only new records, siblings see the same old
journal, and disjoint union preserves records in either order. Every repeated
key is rejected, including identical writes. See [ReplayDrivers.lean](ReplayDrivers.lean).

[RestartingReplay.lean](RestartingReplay.lean) tests the semantic recovery driver
at the worker-local boundary. It injects interruption before and after every
distinct worker-storage boundary in a nested workflow. Another
128 generated pure programs exercise worker crashes, with checks
that the requested faults actually fire. Outcomes and durable journal records
must match direct and sequential evaluation. Targeted cases ensure worker retries
stay inside their spawned function, completed workers return the recorded outcome,
suspension reports stay unchanged, and exhausted runs resume with their saved
state and completed siblings. Duplicate worker assignments are rejected.
Application errors retain source order and never cause crash retries. See
the [recovery model](../LeanCloud/ReplayRecovery.md) for its storage assumptions.

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
Catalog recovery also remembers terminal writers in an unconfigured pool and
blocks replacement finalization until their stop acknowledgements arrive.

Protocol tests check repeated assignment requests, duplicate and stale reports,
empty and partial joins, immutable record creation, JSON codecs, and the different
lifetimes of local database operations and remote requests.
Clearing the inspection tree during a fork/join must leave assignment ownership,
child selection, joining and completion intact: tickets and the recursive
continuation drive execution.
Nested-child replay also runs with a store that rejects ancestor-join reads:
descending into a child must not depend on those records.
Replay tests reject missing prefixes, premature joins, changed requests, malformed
values, and invalid locations without writing records. They count actual `exec`
calls across reconstruction and repeated assignments, check that a losing writer
uses the canonical result, and distinguish IO failures from durable workflow
errors. Codec round trips serialize and parse JSON text. Blob cases cover missing
names, integrity errors, and invalid UTF-8, with and without simulated crashes.

The test build also checks [ProofExamples.lean](ProofExamples.lean), which applies
all three public equivalence theorems to the same nested parallel workflow,
including arbitrary finite worker fault plans. The semantic proofs cover replay
evaluation and worker-local restart. Runtime coordination, message delivery,
process recovery, and deployment behavior are checked by executable tests.

Inbox properties compare real SQLite with `MailboxModel` over 32 generated traces
of 200 operations. They also check SIGKILL recovery, termination signals, HTTP
authentication, lease expiry and renewal, and rejection of stale consumers.
Version tests reject future SQLite schemas without deleting committed mail, and
send legacy and future requests through the real HTTP server. Unsupported requests
must leave the inbox unchanged. Model tests check optional configuration defaults,
bounded retry delays, versioned result envelopes, and future-format rejection.
The native suite also runs the real Pool scheduler over HTTP and SQLite: busy
work retains its assignment, pause revokes it, failed computations stop renewing,
and stale heartbeats cannot renew replacement attempts. A two-worker scheduler
SIGKILL test checks catalog-only persistence, blocks replacement until both stop
acknowledgements arrive, rejects stale reports/tokens, and resumes actual replay
from the root. Existing records survive and the result equals direct evaluation.

Real adapter properties compare 16 generated programs using HTTP/SQLite inboxes,
private scheduler SQLite, and S3 with direct evaluation.
The fixture hosts separate HTTP servers and SQLite databases inside the test
process; only S3 storage runs in a separate container.
Tests also run the real Pool scheduler from durable catalogs before and after
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
The native inbox suite checks confirmed publications across SIGKILL separately.
Container tests exercise actual mailbox transport, multiple worker processes, and
restarts of combined HTTP/SQLite/actor nodes. Chaos plans are generated before
execution and recorded with logs; the seed reproduces the plan, not OS timing.

Run removal tests cover terminal-only admission, durable ID tombstones, late
messages, retry after partial cleanup, and preservation of neighboring runs and
shared user blobs. The real S3 adapter deletes a run with more than one listing
page. Backup model tests reject changing deployments, existing destinations,
corrupt archives, invalid paths, and unsupported versions before importing.
The `--maintenance-only` console suite exercises these commands through the
compiled CLI with real images and volumes, including a paused workflow that
resumes after restore. Its logs are retained with the other CLI command logs.

Console tests cover pause/resume and permanent kill, including interrupted
commands, restart policies, and isolation between runs. Real runtime tests check
that a 35-second computation completes once despite the default 30-second
assignment lease. They also check
that typed process handles observe cancellation, repeated cancellation preserves
the same root record, and a completed result cannot be overwritten by kill.

Arbitrary interacting IO effects need not commute. Differential cases use pure
computations and immutable blob operations; they do not claim that scheduling
preserves the behavior of all user-provided IO actions.
