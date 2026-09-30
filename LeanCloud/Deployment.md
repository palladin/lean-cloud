# Worker deployment

The first runtime runs compiled Lean workflows in separate worker containers,
with PostgreSQL for execution records, RabbitMQ for work items, and SeaweedFS for
S3-compatible shared blobs. All workers use the existing replay interpreter.
There is no separate workflow scheduler.

```text
                         ┌── PostgreSQL ── execution records
application workers ─────┼── RabbitMQ ──── queued and unacknowledged work
                         └── S3 storage ─ immutable blobs and names
```

## Run the example

From the repository root, with Docker and Compose available:

```sh
docker compose up --build -d --scale worker=3
docker compose logs -f worker
```

The build downloads the pinned Lean 4.34.1 toolchain and compiles the application.
Subsequent builds reuse the dependency and compiler caches. The first build can
take several minutes.

Compose waits for the services to become healthy. The submission container seeds
16 log files, creates the run, and publishes its root location. Three workers
then process its locations. The [workflow](../runtime/LeanCloudRuntime/Demo.lean)
splits the files into batches, counts error lines in parallel, and writes a
combined report. Its short `Cloud.exec` sleep makes distribution visible.

After the workers log `completed`, read the report:

```sh
docker compose run --rm --no-deps worker result /etc/lean-cloud/config.json demo
# files=16, errors=24
```

Reading an unfinished run prints `pending` and exits with status 2. Worker logs
include `work LOCATION` for every dequeued item. Each worker exits when it observes
the durable final outcome.

To start another run over the same immutable sample files:

```sh
RUN_ID=demo-2 docker compose up -d --scale worker=3
docker compose run --rm --no-deps worker result /etc/lean-cloud/config.json demo-2
```

`docker compose down` stops the stack and retains its named data volumes. Starting
the same run again reuses its saved records and outcome. Adding `-v` to `down`
deletes those volumes, including all runs and blobs in this local stack.

## Configuration and application entry point

[`deploy/config.json`](../deploy/config.json) supplies three typed configurations:
`db`, `queue`, and `blobs`. It is mounted read-only into each application container.
Use the full example as a template; every JSON field is required. The included
credentials are for the local demo. Supply a private configuration for other
deployments. Service addresses use Compose names (`db`, `queue`, `blobs`). No
service ports are published to the host.

The executable has three commands:

```text
cloud-demo submit CONFIG RUN [INPUT.json]
cloud-demo worker CONFIG RUN
cloud-demo result CONFIG RUN
```

Submission without an input file creates the sample files. A custom input is a
JSON object with `files` (an array of existing global blob names), `batchSize`,
and `pauseMs`. Custom submission does not upload those files. The adapter's
`S3.putBytes` and `S3.name` functions upload and name application inputs.

[`Main.lean`](../runtime/Main.lean) selects the compiled `log-summary/v1` entry
point, decodes its input, and calls `Worker.run`. To run another application,
compile its workflow and entry-point selection into the worker image. Every
worker assigned to a run must use the same program version, codecs, and input.
The stored entry-point version and result schema are checked at startup; version
identifiers are maintained by the application author.

The current executable handles one run per worker invocation. The run identifier
selects both the database namespace and the broker queue; blobs may be shared
across runs. Neither closures nor continuations are sent through the queue.

## Submission, execution, and recovery

[`Run.submit`](../runtime/LeanCloudRuntime/Run.lean) initializes the table and
records the immutable run definition before publishing the root. It waits for
broker confirmation before recording `submitted`. Retrying submission with the
same definition repairs an interrupted publication; a lost reply may duplicate
the root. Reusing a run identifier with a different definition fails. Compose
restarts a failed submission process.

[`Worker.run`](Worker.lean) opens independently owned connections, wraps the raw
database with `JournalDb` and the transport with `LeaseQueue`, then invokes
`LeanCloud.interpret`. It closes acquired connections in reverse order on return
or IO failure. Starting a worker neither initializes a run nor republishes its
root. Compose restarts worker processes that exit unsuccessfully.

The concrete adapters provide these operations:

| Adapter | Persistence and recovery |
| --- | --- |
| [PostgreSQL](../runtime/LeanCloudRuntime/Postgres.lean) | Table creation and parameterized queries use lean-linq's typed schema. A unique `(run, key)` constraint admits one immutable record. Repeating the same value succeeds; a different value is rejected. Sibling results have separate keys. |
| [RabbitMQ](../runtime/LeanCloudRuntime/RabbitMQ.lean) | Durable quorum queues, persistent messages, confirmed mandatory publication, prefetch one, and manual acknowledgements. Closing a connection leaves unacknowledged work eligible for redelivery. Receipts include their connection identity. |
| [S3](../runtime/LeanCloudRuntime/S3.lean) | SHA-256 content keys and conditional immutable writes; reads verify size and hashes. Global names are immutable records pointing to blob references. |

The interpreter persists results and publishes successor work before acknowledging
the current delivery. It records the final outcome under the run's `completed`
key before acknowledging completion. A replacement worker reconstructs execution
using these records and the original input. An idle queue response means wait,
not workflow completion.

A hard process kill bypasses cleanup. The broker recovers its unacknowledged
deliveries, while the database and blob service retain their data. Arbitrary
`Cloud.exec` actions can run again if their result was not recorded before a
crash; applications must account for repeated external actions.

## Validation

Run the ordinary Lean tests with `lake test`. Run the real services separately:

```sh
lake exe cloud_runtime_tests
```

This Lean test driver builds the images and owns an isolated Compose project. It checks
generated table creation and constraints, database write conflicts, queue
redelivery and stale receipts, and immutable blob round trips. It compares 32
generated pure programs through direct evaluation,
simulated replay, and the real worker backend, including replay of completed runs.
It also requires multiple worker containers to process the file example, kills a
worker during an action, and verifies reports after all three services restart.
The driver removes only its own containers and data volumes.

Inject random worker crashes with the Lean chaos driver and Docker:

```sh
lake exe cloud_chaos --seed 1
lake exe cloud_chaos --seed 42 --crashes 20 --workers 4 --no-build
```

The [chaos driver](../LeanCloudTests/Chaos.lean) generates a seeded sequence of
worker selections and delays. Both drivers use Lean's `IO.Process` to run Docker.
It uses `SIGKILL` and starts fresh worker processes against the same durable
services. After this bounded fault period, all workers must finish within the
timeout, the saved report must be correct, and a fresh worker must retrieve the
saved outcome. A test that kills no worker fails. Each invocation has isolated
services and preserves its plan, event log, and container logs in the printed
temporary directory before removing its containers and volumes.

The seed reproduces the injection plan, not exact network timing or interpreter
boundaries. The SimM tests provide controlled boundary exploration. The current
real chaos workload is the file example; generated pure programs are exercised
separately by the differential integration tests. Service crashes and network
partitions during execution are not yet randomized.

These tests provide evidence for adapter behavior. They do not prove the real
services refine the simulation or guarantee fairness. The existing equivalence
theorem concerns pure workflows under its stated backend and scheduling laws.

## Current limits

This is a first local and single-host on-premises runtime. The services each have
one container and persistent volumes; this is not a highly available cluster.
The RabbitMQ client currently uses plain TCP, with heartbeats disabled and a
one-hour consumer acknowledgement timeout in the supplied broker configuration.
Worker process death is tested; prompt detection of partitions and hung workers
needs additional transport work. The blob adapter uses buffered curl requests
with SigV4 signing, without streaming or multipart upload.

The Linux container path has been exercised on ARM64. The Dockerfile also selects
the AMD64 Lean distribution, but that build has not been tested here. Native
macOS deployment is not part of this first runtime.

The same interpreter can use hosted services through appropriate adapters.
Native AWS SQS and Azure queue/blob adapters, managed identities, broker TLS,
multi-host orchestration, and completed-run cleanup remain future work. The
current S3 implementation has been tested against the included SeaweedFS service.

Runtime dependencies live in a separate [Lake package](../runtime/lakefile.lean),
so core builds and proofs do not require native service libraries. The pinned
upstream lean-linq revision includes Lean 4.34.1 support and typed table creation;
the runtime initializes its PostgreSQL schema directly through that API.
