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

Removing a run clears replay records and the last views on every active worker
and the scheduler. Partial failures are reported; retry `remove` after restoring
the unavailable node. Scaled-down workers clear retired-run views on their next
startup. Shared application blobs are retained.

Public client credentials are separate from internal node credentials. Provider
login stays outside Lean Cloud; deployed cloud nodes use workload identities.
Only expose `/deployment` through a public authenticated HTTPS endpoint. Internal
mailbox, administration and telemetry routes remain private.
