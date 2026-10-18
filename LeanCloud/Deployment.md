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

`Cloud.exec` receives an `Environment` with `currentWorker` and `workers`.
Each worker has an `id`, a `cpus` concurrency budget, and optional `memoryMiB`.
The runtime refreshes this snapshot once per assignment. It describes configured
pool capacity, not currently idle workers or free memory. Visible container
limits can lower the executing worker's budget.

Use `Cloud.parallel fun env => ...` to partition work using a recorded pool
snapshot, and `Cloud.exec fun env => ...` to use the executing worker's resources:

```lean
def batches (items : Array Nat) (process : Nat → Array Nat → IO Nat) :
    Cloud IO (Array Nat) := cloud {
  Cloud.parallel fun planning =>
    let count := max 1 (min items.size planning.workers.size)
    let width := (items.size + count - 1) / count
    (Array.range count).map fun i => cloud {
      Cloud.exec fun executing =>
        process executing.currentWorker.cpus
          (items.extract (i * width) ((i + 1) * width))
    }
}
```

Here `process` is your local computation; its first argument is the number of
concurrent jobs it may use. Lean Cloud does not automatically parallelize that
computation or pin it to a CPU. A planned branch can execute on any worker, so
use the executing worker's budget inside `exec`.

Parallel planning records its environment through an ordinary `exec` before
forking. Replay reuses it, preserving the original branches after a pool change.
An ordinary `exec` records only its outcome: a completed call is never invoked
on replay; an interrupted, uncommitted call receives its replacement attempt's
environment. Exceptions from the user computation remain recorded failures.

For fixed branches, use `Cloud.parallel fun _ => #[...]`. A named planning
function is passed directly as `Cloud.parallel plan`. The `||` operator still
combines two fixed branches. No environment primitive or new parallel effect
is needed. See [resource settings](../deploy/README.md#worker-resource-budgets)
for deployment configuration.

Removing a run clears replay records and the last views on every active worker
and the scheduler. Partial failures are reported; retry `remove` after restoring
the unavailable node. Scaled-down workers clear retired-run views on their next
startup. Shared application blobs are retained.

Public client credentials are separate from internal node credentials. Provider
login stays outside Lean Cloud; deployed cloud nodes use workload identities.
Only expose `/deployment` through a public authenticated HTTPS endpoint. Internal
mailbox, administration and telemetry routes remain private.
