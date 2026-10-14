# Runtime deployment

Each node runs the Lean application, an HTTP inbox and SQLite in one process.
The scheduler organizes work; workers write immutable replay records to shared
blob storage. Each node owns its durable SQLite volume. Application registration
is in `LeanCloudRuntime.Application`; users supply a registry to `Application.main`.

The cloud console communicates only with the scheduler's authenticated
`/deployment` API. Local Docker, existing Kubernetes and Azure deployments
use this same client path. Infrastructure management is external and replaceable.

See [deployment helpers and examples](../deploy/README.md) for inspectable shell
scripts, Compose generation, Kubernetes resources and OpenTofu modules.
The [Azure walkthrough](../deploy/Azure.md) covers provisioning through cleanup.
See [console commands](Console.md) for workflow operations.

Deployment tooling must preserve stable node IDs, isolated durable inbox volumes,
shared immutable blob records, and application image identity. Stop old attempts
before replacing the same node; a timeout alone does not prove a worker stopped.
The provided helpers use a full stop/start barrier and reject missing known
volumes. No scheduler tree is persisted: recovery reconstructs it through replay.

Public client credentials are separate from internal node credentials. Provider
login stays outside Lean Cloud; deployed cloud nodes use workload identities.
Only expose `/deployment` through a public authenticated HTTPS endpoint. Internal
mailbox, administration and telemetry routes remain private.
