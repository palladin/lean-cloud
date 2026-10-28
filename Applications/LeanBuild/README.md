# LeanBuild

Build a Lean project from GitHub on lean-cloud. Give it a repository, revision,
and Lake targets. Workers compile ready modules using their local CPUs and share
artifacts through blob storage. The final report links to the completed workspace,
executables, and diagnostics. Lean's normal elaboration and kernel checking run
as part of compilation.

```json
{
  "repository": "https://github.com/leanprover-community/batteries",
  "revision": "66e469188fe07963e5cf666c7d4433f45b8131c5",
  "targets": ["+Batteries.Data.Nat.Bisect", "+Batteries.Data.Nat.Bitwise.Lemmas"]
}
```

Omit `targets` to build the project's default Lake targets. Use the same names as
`lake build`: for example `Mathlib`, `my_executable`, `+My.Module:olean`, or
`@dependency/Library`. Custom targets are supported too. A branch or tag is
resolved once; the actual commit is recorded in the result.

## How it runs

The Cloud workflow has five stages:

1. Fetch the revision, resolve Lake dependencies and generated-source prerequisites,
   discover the module DAG, and publish the prepared workspace.
2. Enqueue modules with no prerequisites. Record the number of builder sessions
   from `env.workers.size`.
3. Run the builder sessions in one `Cloud.parallel`. Each is a long-lived `exec`
   that continuously feeds ready modules to one persistent Lake session.
4. Collect the immutable result for every planned module. Failed modules block
   their dependents; independent modules can still finish.
5. Restore the artifacts on one worker and ask Lake to complete the original
   targets, including native compilation, linking, custom targets and dynamic
   dependencies. Publish the complete workspace manifest.

Each builder restores the prepared sources once and loads Lake once. A bounded
pipeline receives ready work, restores missing prerequisites, compiles modules
and publishes their artifacts concurrently. Small queue receives fill available
capacity immediately; they do not define execution batches. Shared prerequisite
files are transferred once, and concurrent preparations await the same transfer.

Every worker also follows a durable completion feed with its own cursor and
prefetches new artifacts while Lake is busy. Dequeuing a module waits only for
prerequisites still in flight. The feed announces module names; artifact bytes
travel directly from blob storage. Read and upload pools each allow up to
`min 32 (max 4 (4 × CPUs))` concurrent transfers, shared across nested operations.
Compilation still uses `max 1 (CPUs − 1)` slots.

As each module finishes, a bounded IO pool packs and uploads its artifacts, publishes
its immutable result, notifies ready dependents, and acknowledges its delivery.
Each module stays in one pack; parallel transfers do not split its small files
into separate objects. Large packs upload chunks concurrently.
Uploads overlap both other uploads and ongoing compilation. All claims are renewed
until settled. The workspace, manifest cache and downloaded packs stay on the
worker's local filesystem; already installed imports are not copied again.

For `Base → [Left, Right] → Final`, publishing `Base` makes `Left` and `Right`
available immediately. `Final` becomes available when both are committed.
Any worker, including the one compiling `Left`, can start newly ready work while
its other modules are still compiling or uploading. A compilation completion
immediately frees a slot. There are no batch barriers, global dependency rounds
or repeated Cloud forks for module scheduling.

The queue lives in the scheduler's existing HTTP/SQLite service. Its short
transactions run independently of the Cloud scheduler actor. All deployments
use the same implementation; no SQS, Service Bus, or separate queue service is
required. Sources, artifacts and module results move directly between workers
and blob storage, not through the scheduler.

Module names are idempotent queue keys: several parents can announce the same
ready module without creating more work, even after its acknowledgement.
Queue deliveries have renewable leases and may repeat. Artifacts are uploaded
before publishing an immutable, run-scoped result; notifications precede ACK.
After interruption, redelivery reuses a committed result and repeats any needed
notifications. An empty receive is not completion: builders wait until the queue
has no pending **or leased** messages, and the collection stage still requires
one result for every module. This relies on seeding all roots before starting
builders and sending every successor before acknowledging its predecessor.

Pause or kill signals `env.cancellation`. Builders stop accepting work, terminate
active compiler process groups, join local tasks, and release outstanding work.
The runtime checks assignment ownership before journaling the `exec` outcome.
Ordinary IO exceptions remain application failures; they are not crash retries.
HTTP clients retry transient connection failures and temporary service responses
with bounded backoff and jitter before reporting an exhausted operation as an error.

`watch` shows one shared module completion counter and each worker's compiling,
restoring, ready and publishing counts. Failed/blocked modules are included in
completed work and displayed separately. The service updates the durable counter
atomically with settlement; repeated acknowledgements cannot inflate it. Workers
report snapshots approximately once per second independently of compilation.
Watch selects the newest counter revision and marks stalled activity updates stale.
Finalization
reports its current phase: gathering manifests, restoring artifacts, completing
Lake targets, verifying the workspace, or publishing the result.
Displayed progress is a best-effort last view, separate from replay records.

## Local deployment and first run

From the lean-cloud repository:

```sh
bash Applications/LeanBuild/build.sh lean-cloud-build:dev
bash deploy/local.sh configure .lean-cloud/build lean-cloud-build:dev build 3 8080
bash deploy/local.sh up .lean-cloud/build
lake exe lean_cloud
```

In the console, enter each command separately:

```text
connect build http://127.0.0.1:8080 --token-file .lean-cloud/build/client.token
programs
run lean-build --input Applications/LeanBuild/example.json --id batteries
ps
watch batteries
result batteries
```

The example builds two modules from a pinned Batteries revision. The same image
works with the [Azure](../../deploy/Azure.md), [AWS](../../deploy/AWS.md), and
[existing Kubernetes](../../deploy/README.md) deployment helpers; the console
uses the same HTTP connection in each environment.

The report contains:

- `commit`, `toolchain`, `platform`, and `source`: exact input provenance.
- `modules`: per-module status, diagnostics, elapsed time and artifact manifest,
  in dependency order. Module durations run from their submission to Lake
  through compilation completion; they include waiting for Lake jobs and are not
  CPU time. Failed prerequisites produce `blocked` results.
- `build`: final Lake target status, diagnostics, duration and an `artifacts`
  reference to the complete workspace manifest. Its duration includes final
  artifact publication and the local cache checkpoint.
- `success`: true only when the modules and final target build succeed.

Save a diagnostics or manifest reference from the report as JSON, then read it:

```sh
bash Applications/LeanBuild/local-files.sh .lean-cloud/build ref.json
```

Each manifest entry records a relative path, a packed-file reference (pack,
offset, length, SHA-256), and an executable flag. `files download CONFIG FILE_REF
OUTPUT` downloads a top-level file reference; `files restore CONFIG MANIFEST_REF
DIRECTORY` restores a workspace into a new directory. These application commands
run inside the deployed image, where storage is configured. Transfers verify
sizes and hashes. Native executables require a compatible platform and libraries.

Remove the test deployment and its stored data:

```sh
bash deploy/local.sh clean .lean-cloud/build --yes
```

## Configuration and resource use

| Request field | Meaning | Default |
| --- | --- | --- |
| `repository`, `revision` | Public GitHub HTTPS URL and Git revision | Required |
| `targets` | Arguments to `lake build` | Project's default targets |
| `subdirectory` | Lake project directory inside the repository | `"."` |
| `options` | Lake configuration values, e.g. `{"feature":"enabled"}` passes `-Kfeature=enabled` | `{}` |
| `cache` | `"rebuild"` clears package build directories and disables external Lake caches; `"reuse"` allows valid prepared cache artifacts | `"rebuild"` |
| `limits` | Command and artifact limits | Below |

Builder count is recorded once. Each builder uses its executing worker's current
CPU budget, so a restarted session may have a different local width. These are
concurrency budgets, not CPU affinity or placement guarantees. An N-CPU worker
uses `max 1 (N - 1)` compilation slots, leaving headroom for coordination and
artifact processing. Individual module compilers default to one thread so they
do not each create a hardware-sized pool. Preparation and final
targets also use the full budget. Native tools and project options may create
additional threads; container limits remain authoritative.

Configure `cpuMillis` and `memoryMiB` in `deployment.json` (see
[worker resource budgets](../../deploy/README.md#worker-resource-budgets)). An
unconfigured worker advertises one CPU. The local pool does not dynamically
estimate module memory use: choose enough memory for the concurrent compilers.
Artifact hashing, restoration and blob transfers also use bounded local pools.

`limits` defaults to `seconds: 600` per subprocess, `helperMemoryMiB: 4096` per
Lake helper, `bytes: 2147483648` per workspace, and `modules: 10000`.
The time limit covers the persistent Lake session, not each module individually; the final
Lake invocation has its own limit. Diagnostics are capped at 16 MiB per stream. Workspace size is checked at
preparation, restoration/publication boundaries and after all local compilers
stop. Container memory and disk limits bound peak usage between these checks.

Workers cache immutable packs in `/data/build-cache` and one reusable workspace
in `/data/build-cache.workspace`. The workspace key includes prepared sources,
request, toolchain and helper. Switching builds replaces it. Cache hits are
verified; an interrupted session leaves no clean marker and is reconstructed
from committed blob artifacts. Cache directories must be private to each worker
process. `LEAN_BUILD_CACHE` changes the pack directory and
`LEAN_BUILD_CACHE_BYTES` bounds packs (default 4 GiB). Without a cache, builders
use temporary workspaces. Provision extra disk for logs and temporary files.
Concurrent readers share a pack download; independent packs download in parallel.
Packs stay pinned while being copied. When active packs fill the cache, additional
downloads use temporary space rather than evicting a pack still in use.

Prepared inputs and installed artifacts remain immutable during module builds.
Conflicting artifacts are rejected. Build hooks must declare dependencies to Lake
and work in relocated workspaces. Custom targets and unusual facets remain the
final Lake build's responsibility. Dependencies must be inside the snapshot;
internal file symlinks are materialized, while external links, directory links,
Git submodules and external dependency directories are rejected.

## Toolchains and compatibility

Source projects need a stable Lean **4.35.0 or later** release. The project's
`lean-toolchain` must match the deployed toolchain exactly; it is never rewritten.
To select an exact release:

```sh
bash Applications/LeanBuild/build.sh lean-cloud-build:dev 4.35.0
```

The image pins the release checksum. Each worker downloads Lean directly from
GitHub at first startup, verifies it and checks the Lake helper. Restarts reuse
`/data/toolchains`; the scheduler does not download a toolchain. Lean 4.35.0 needs
roughly 3.2 GB of persistent space plus installation scratch space. Kubernetes
can use `startupSeconds: 900` to allow installation time. Alternatively,
`LEAN_BUILD_TOOLCHAIN` selects an existing installation. `LEAN_BUILD_RELEASE`
and `LEAN_BUILD_TOOLCHAINS` select the pinned release JSON and download cache.
4.35.0 is tested; future Lake API changes may need helper updates.

The workflow is `lean-build/v6`. Start new runs with the new image; unfinished
older workflows must keep their original image. `modulesPerJob` is removed.
Packed manifests remain compatible with v2. Independent checking fields are no
longer accepted; use `limits.helperMemoryMiB` instead of `checkerMemoryMiB`.

Run trusted repositories in dedicated deployments: Lake configuration, build
hooks, plugins and metaprograms execute code inside the worker container.

## Tests

```sh
cd Applications/LeanBuild
elan toolchain install "$(cat source-toolchain)"
export LEAN_BUILD_TOOLCHAIN="$(elan run "$(cat source-toolchain)" lean --print-prefix)"
export LEAN_BUILD_HELPER="$PWD/Helper.lean"
lake build cloud_app build_local build_tests
.lake/build/bin/build_tests --native
```

Tests compare direct/replay execution on 40 generated DAGs. They cover concurrent
builder sessions, progress without round barriers, interruption between result
publication and notification, cancellation, blocked dependencies, durable errors,
cache reuse and integrity. A native rendezvous verifies concurrent publications
while another compiler in the same session is still running. A single-worker
rendezvous checks that newly ready dependencies advance before an unrelated slow
compiler completes. Native fixtures compare output with ordinary Lake and
cover libraries, executables, C FFI, generated/custom targets and restored artifacts.
Runtime tests separately exercise the same HTTP/SQLite queue's leases, reopening,
stale receipts, concurrent consumers and run removal.

The container test uses the ordinary HTTP client and removes its temporary
deployment on exit:

```sh
bash Applications/LeanBuild/test-deployment.sh lean-cloud-build:dev
```

The continuous builder has not yet been benchmarked on the full Mathlib DAG in a
cloud deployment. Shared queue throughput, artifact IO, module memory use and the
final target build can still limit utilization. Finalization merges manifests in
one pass, verifies files concurrently, retains existing entries from that scan,
and uploads the final manifest in parallel chunks. Unchanged artifacts keep their
original blob references.
