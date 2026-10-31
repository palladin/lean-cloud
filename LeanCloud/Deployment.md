# Runtime deployment

Each node runs the Lean application, an HTTP inbox and SQLite in one process.
The scheduler organizes work; workers write immutable replay records to shared
blob storage. Each node owns its durable SQLite volume. Application registration
is in `LeanCloudRuntime.Application`; users supply a registry to `Application.main`.

The cloud console communicates only with the scheduler's authenticated
`/deployment` API. Local Docker, existing Kubernetes, Azure and AWS deployments
use this same client path. Infrastructure management is external and replaceable.

See [deployment helpers and examples](../deploy/README.md) for inspectable shell
scripts, Compose generation, Kubernetes resources and OpenTofu modules.
The [Azure walkthrough](../deploy/Azure.md) covers provisioning through cleanup.
The [AWS walkthrough](../deploy/AWS.md) uses the same Kubernetes deployment flow.
See [console commands](Console.md) for workflow operations.

Deployment tooling must preserve stable node IDs, isolated durable inbox volumes,
shared immutable blob records, and application image identity. Stop old attempts
before replacing the same node; a timeout alone does not prove a worker stopped.
The provided helpers use a full stop/start barrier and reject missing known
volumes. No scheduler tree is persisted: recovery reconstructs it through replay.

Workers cache confirmed immutable replay records across assignments. Each node
defaults to at most 64 MiB of encoded records and keys, and 4,096 entries; map
overhead is additional. Set `worker.replayCacheBytes` and
`worker.replayCacheEntries` in the runtime configuration to change these budgets.
Either value can be zero to disable caching. The cache is disposable memory:
restarts read the global journal again. Every cache hit still checks assignment
ownership, and creates always publish to durable storage before caching a value.

## Planning work and using local resources

`Cloud.exec` receives `Environment IO`: worker capacity, `blobs`, `queues`,
`cancellation`, and `progress`. Each capability is supplied explicitly; pure
models use no-op cancellation/progress and an unsupported-queue adapter.
Each worker advertises an `id`, a `cpus` concurrency budget, and optional
`memoryMiB`. The runtime refreshes capacity once per assignment; these are
configured budgets, not instantaneous utilization or free memory.

`Cloud.parallel` takes an array. When planning depends on capacity, explicitly
record only the data you need:

```lean
def batches (items : Array Nat) (process : Nat → Array Nat → IO Nat) :
    Cloud IO (Array Nat) := cloud {
  let workers ← Cloud.exec (fun env => pure env.workers.size) "plan"
  let count := max 1 (min items.size workers)
  let width := (items.size + count - 1) / count
  Cloud.parallel ((Array.range count).map fun i =>
    Cloud.exec fun env =>
      process env.currentWorker.cpus
        (items.extract (i * width) ((i + 1) * width)))
}
```

Replay reuses the recorded worker count, preserving the planned branches after a
pool change. Each unrecorded `exec` receives the executing worker's current
context. A branch may execute on any worker; CPU budgets do not pin placement.
For fixed branches, use `Cloud.parallel #[...]` or `left || right`.

Blob operations are ordinary IO inside `exec`: `env.blobs.putBlob`, `readBlob`,
`resolveBlob`, `putText`, `readText`, and `readTextByName`. User code can run them
concurrently with local tasks. Join all those tasks before returning. Only the
final `exec` result is recorded, so large reads and intermediate values stay out
of the journal. `Environment` contains capabilities and has no codec; return
serializable capacity data or blob references instead.

An uncaught IO exception becomes a recorded application failure. To handle or
retry it, catch it inside `exec`. A worker crash before the result is committed
can repeat the entire body, including blob writes; design those actions to
support repetition. A committed result is reused without executing the body.
Replay-journal failures remain outside this user exception boundary.

Long-running bodies can poll `env.cancellation.isRequested` and report an
absolute last view with `env.progress.report "activity" { message := "…" }`.
Progress may include `completed` and `total`; it is best-effort telemetry, not
durable state. Use a small, fixed set of activity names. Pause, kill, or loss of
assignment ownership signals cancellation. Stop and join local tasks before
returning; the runtime refuses to journal an outcome after revocation.

`env.queues.open "name"` opens a run-scoped work queue. It provides batched
`send`/`receive`, read-only `peek`, `acknowledge`, `renew`, `release`, and `isIdle`. Deliveries have
renewable leases and may repeat. An empty receive can mean other consumers still
hold leases; even `isIdle` only means there are currently no pending or leased
messages, not that future producers are finished. Applications own their
completion protocol and must make repeated work safe.

Each sent item has a stable `key`, JSON `value`, and optional `priority` (default
zero). Receive selects the highest priority first, using FIFO for ties. Sending
the same key, value and priority again is a no-op, including after acknowledgement;
changing its value or priority is an error. This lets multiple parents safely
announce the same ready task. Keys
and their deduplication records live until the run is removed.

`peek none count` observes available work in receive order without taking leases.
Continue with the last item's `position` to read beyond a page, even if earlier
items were removed. Pages are live observations rather than a snapshot: start
again at `none` to see new work ahead of a previous position. Peeking never
prevents another worker from receiving the observed work.

The runtime hosts these queues in the scheduler's existing HTTP/SQLite service.
Queue transactions run independently of the Cloud actor loop. Local, Azure and
AWS use the same adapter, with no additional queue service. Queue transport
errors inside `exec` are ordinary IO failures, like blob errors.

For resumable application work, `env.blobs.readNamed` and `publishNamed` expose
immutable, run-scoped result names. Publication atomically selects one blob
reference; subsequent publications return that reference. These are application
records, separate from the interpreter's replay locations. Publish artifacts
before their named result, and enqueue successors before acknowledging work.
See [LeanBuild](../Applications/LeanBuild/README.md) for a complete example.

Blob bytes use SHA-256 content keys and conditional creation. Duplicate uploads
check the existing object's length without downloading it; name publication
also uses metadata only. This relies on SHA-256 collision resistance. Reads
verify both the content hash and the reference checksum. Small replay and named
result records still return the canonical value selected by the first writer.
Storage transfers use pooled libcurl connections, without subprocesses or
temporary files. Large file transfers retain bounded chunk buffers and hash
their contents while streaming.

See [resource settings](../deploy/README.md#worker-resource-budgets) for deployment
configuration. Existing unfinished workflows must continue with their original
image: removing implicit planning and blob records changes replay locations.

Removing a run clears replay records and the last views on every active worker
and the scheduler, including run-scoped queues and named result references.
Partial failures are reported; retry `remove` after restoring
the unavailable node. Scaled-down workers clear retired-run views on their next
startup. Shared application blobs are retained.

Public client credentials are separate from internal node credentials. Provider
login stays outside Lean Cloud; deployed cloud nodes use workload identities.
Only expose `/deployment` through a public authenticated HTTPS endpoint. Internal
mailbox, administration and telemetry routes remain private.
