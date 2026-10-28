# Deploying Lean Cloud

The console is an HTTP client. These optional shell helpers build and deploy
nodes; you can inspect, edit, or replace them with your own tooling. An existing
Kubernetes cluster needs no cloud provisioning helper.

Start with [local Docker](#local-docker), or follow the separate
[Azure walkthrough](Azure.md) or [AWS walkthrough](AWS.md) to run the same example on Kubernetes.

All follow **check tools → build → configure → up → connect → run**.
Azure and AWS add explicit login, infrastructure provisioning, and image publishing.
Once configured, the deployment commands have the same shape:

| Action | Local Docker | Azure / AWS / Kubernetes |
| --- | --- | --- |
| Inspect configuration | `./deploy/local.sh show DIR` | `./deploy/kubernetes.sh show DIR` |
| Start / restart | `./deploy/local.sh up DIR` | `./deploy/kubernetes.sh up DIR` |
| Inspect nodes | `./deploy/local.sh status DIR` | `./deploy/kubernetes.sh status DIR` |
| Get the console connection | `./deploy/local.sh connect DIR` | `./deploy/kubernetes.sh connect DIR 8081` |
| Set worker count | `./deploy/local.sh scale DIR 5` | `./deploy/kubernetes.sh scale DIR 5` |
| Stop; keep data | `./deploy/local.sh down DIR` | `./deploy/kubernetes.sh down DIR` |
| Delete deployment data | `./deploy/local.sh clean DIR --yes` | `./deploy/kubernetes.sh clean DIR --yes` |

Local `connect` prints the connection command and exits. Kubernetes `connect`
keeps a private tunnel open. Local `clean` also deletes the local blob service;
Kubernetes `clean` leaves shared blobs and infrastructure for separate cleanup.

## Local Docker

You need:

- Docker with Compose and Buildx, with its engine running.
- `jq`, `openssl`, and `shasum`.
- [Lean via elan](https://lean-lang.org/install/), a C compiler and libcurl
  headers/runtime to build the console. On macOS, install the Xcode Command Line
  Tools; on Ubuntu, install `build-essential` and `libcurl4-openssl-dev`.

Run these commands in your shell, from the repository directory. Lake uses the
version in `lean-toolchain`. The application itself builds inside Docker.
Use a fresh `.deployment` directory and an unused local port (8080 below).

```sh
./deploy/local.sh doctor
./deploy/build.sh . lean-cloud-demo:dev
./deploy/local.sh configure .deployment lean-cloud-demo:dev development 3 8080
./deploy/local.sh show .deployment
# Review .deployment/compose.json and .deployment/config.json.
./deploy/local.sh up .deployment
./deploy/local.sh status .deployment
./deploy/local.sh connect .deployment
```

This starts one scheduler, three workers and local blob storage. Wait for the
helper to report that the nodes are healthy, then open the console. Lake builds
it automatically on the first run:

```sh
lake exe lean_cloud
```

Continue with [the log-processing example](#run-the-log-processing-example)
to submit and watch your first workflow.

`configure` only prepares files and pins the local image ID; `up` starts the
containers. The old `init` spelling remains an alias for `configure`.
`show` displays deployment settings without printing authentication tokens.

Each node hosts its HTTP inbox and embedded SQLite database. Submitting a run
uses these existing nodes. Only the scheduler port is published, on loopback.
Client and internal tokens are separate; the deployment directory is private.
Its runtime config is readable inside the container by the unprivileged worker.
The helper generates separate random client, mailbox, and blob credentials for
each deployment. The fixed values in `deploy/config.json` and `deploy/s3.json`
are used only by the repository's isolated Compose test fixture.

## Run the log-processing example

Start the [local deployment](#local-docker) above, then enter these commands in
the cloud console:

```text
connect development http://127.0.0.1:8080 --token-file .deployment/client.token
programs
run log-summary --id my-logs
ps
watch my-logs
```

The bundled application creates 16 sample log files in blob storage and processes
them in parallel batches. `watch` shows the branch tree, source code, and workers.
Press `q` to return to the prompt, then read the completed report:

```text
result my-logs
```

If the run is still running, wait until `ps` shows `completed`, then try `result`
again. Use a different `--id` to start another run; the ID identifies one workflow.

Expected output:

```text
files=16, errors=24
```

See the [workflow](../runtime/LeanCloudRuntime/Demo.lean) and
[console guide](../LeanCloud/Console.md). For a remote deployment, connect to its
scheduler endpoint instead; the workflow commands are the same.

## Manage the local deployment

After trying the example, type `quit` to leave the console. These are **shell**
commands for inspecting, resizing, stopping or removing the deployment:

```sh
./deploy/local.sh status .deployment
./deploy/local.sh scale .deployment 5
./deploy/local.sh down .deployment    # stop; keep data
./deploy/local.sh up .deployment      # recover
./deploy/local.sh clean .deployment --yes  # delete containers and all local data
```

This initial helper scales with a full stop/start barrier. It preserves retired
worker volumes. It does not infer that an unreachable worker has stopped.
Images are resolved to immutable IDs at initialization. Use a new deployment for
new application code; changing the code of an existing replay journal is unsafe.
The helpers refuse to start if a previously recorded durable volume is missing.
Helpers protect their state directories with mode 0700 and a local `.gitignore`,
including when you choose a custom directory name. Generated applications also
exclude credentials, provider state, and generated configs from Docker contexts.
Keep these exclusions when supplying your own build files. `clean` retains
the inspectable configuration; choose a fresh directory to deploy again.

## Worker resource budgets

Set `cpuMillis` and `memoryMiB` in `deployment.json`, for example `6000` and
`8192` for six CPUs and 8 GiB per worker. Kubernetes uses CPU requests and memory
limits; local Docker uses CPU and memory limits when these fields are supplied.
Local defaults leave Docker resources unrestricted and advertise a conservative
one-job CPU budget. The runtime uses any visible memory limit when no budget is
configured.

On Kubernetes, optional `cpuRequestMillis` sets the worker's placement request
separately from its `cpuMillis` execution budget; it defaults to `cpuMillis`.
For one worker on an 8-vCPU node, use `cpuMillis: 8000` and
`cpuRequestMillis: 7000`. LeanBuild then runs seven compilers, leaving the remaining
CPU capacity for coordination, artifact IO and node services. The request allows
the pod to fit beside Kubernetes services; it is not a second execution limit.
Kubernetes workers have no CPU quota, so this assumes dedicated capacity and is
not CPU pinning or an eight-core guarantee on an oversubscribed node.

The same settings reach the workflow through `env.currentWorker` and
`env.workers`; `cpus` is `floor(cpuMillis / 1000)`, with a minimum of one job.
This is a concurrency budget, not CPU pinning or a count of idle cores. See the
[environment example](../LeanCloud/Deployment.md#planning-work-and-using-local-resources).

After editing these fields, apply them through `scale` with the desired worker
count, even if that count is unchanged:

```sh
./deploy/local.sh scale .deployment 3
# Or, for Kubernetes (including Azure and AWS):
./deploy/kubernetes.sh scale .kube-deployment 3
```

This stops old nodes before updating the runtime configuration and starting
replacements. Kubernetes also supports separate `schedulerResources`, described below.

## Your application

```sh
./deploy/new-app.sh ../my-app "$PWD"
# Edit ../my-app/Main.lean: register your CloudProgram values.
./deploy/build.sh ../my-app my-app:dev cloud_app "$PWD"
./deploy/local.sh configure .my-app-deployment my-app:dev my-app 3 8081
./deploy/local.sh up .my-app-deployment
```

`Main.lean` delegates to `Application.main registry args`. The same executable
serves either a scheduler or a worker. `deploy/app/Dockerfile` is an ordinary
Buildx Dockerfile with explicit SDK and node source contexts. Building and
publishing for a remote architecture uses the same build helper:

```sh
./deploy/build.sh --platform linux/arm64 ../my-app my-app:dev
./deploy/azure.sh publish .azure-infra my-app:dev VERSION
```

For Azure, first follow the [cluster setup](Azure.md); `publish` uses your existing
login. `azure.sh configure` resolves the published image to an immutable digest.
With another registry, use its normal image publishing tools and supply the
resulting digest (`IMAGE@sha256:...`) in Kubernetes.

## Existing Kubernetes cluster

Requires `kubectl`, `jq`, `openssl`, and `shasum`. Authentication and cluster
context setup belong to your environment. The helper manages a dedicated
namespace, one StatefulSet and durable PVC per node, and private ClusterIP
services. The source template is `deploy/kubernetes/resources.jq`.

```sh
mkdir -m 700 .kube-deployment
cp deploy/kubernetes/deployment.example.json .kube-deployment/deployment.json
# Edit context, namespace, immutable image, worker count and resource settings.
# Supply .kube-deployment/storage.json for your shared blob service (examples below).
./deploy/kubernetes.sh render .kube-deployment
# Review .kube-deployment/resources.json; render does not contact Kubernetes.
./deploy/kubernetes.sh up .kube-deployment
./deploy/kubernetes.sh status .kube-deployment
./deploy/kubernetes.sh connect .kube-deployment
```

`status` lists the cluster machines and the deployment's pods. An optional
`kubeconfig` path in deployment.json pins the credentials file, so commands do
not depend on your shell's current Kubernetes configuration. The Azure and AWS
configure helpers fill this in automatically.

`connect` runs a foreground loopback port-forward and prints the console command.
Its optional final argument selects the local port, for example
`./deploy/kubernetes.sh connect .kube-deployment 8081` (default: 8080).
Keep it running in another terminal. If the scheduler pod restarts or the tunnel
disconnects, run `connect` again; saved CLI profiles still use the same address.

`cpuMillis` and `memoryMiB` size each node. For applications with large workers,
`"schedulerResources": {"cpuMillis": 250, "memoryMiB": 512}` can give the scheduler
smaller requests and a smaller memory limit. Omitted fields use the node defaults.

Applications that install tools at startup can set `startupSeconds` in
`deployment.json` (default 300, range 5–3600). This controls the startup probe
and the helper's readiness wait. For LeanBuild's first toolchain download, use 900.
Your own authenticated HTTPS gateway may
expose `/deployment` instead; never expose internal `/app`, `/mailbox` or
`/telemetry` routes publicly. The CLI accepts HTTPS, or HTTP on loopback only.

For Azure workload identity, use:

```json
{"provider":"azure","endpoint":"https://ACCOUNT.blob.core.windows.net","container":"cloud","authentication":{"kind":"workload"}}
```

Set `serviceAccountAnnotations` to
`azure.workload.identity/client-id` and `azure.workload.identity/tenant-id`, and
`podLabels` to `{"azure.workload.identity/use":"true"}` in deployment.json.
An S3-compatible service can instead use `accessKey` and `secretKey` in the
private storage.json file. The bucket/container must already exist when marked
provisioned. With Azure workload identity, nodes obtain credentials themselves;
no storage key is needed in the configuration.

To change worker count, use the same command as locally:

```sh
./deploy/kubernetes.sh scale .kube-deployment 5
```

The helper updates deployment.json after stopping all old pods, and waits for
their deletion before any replacement starts. It
records PVC UIDs and rejects missing/replaced claims. Operations are serialized
with the `cloud-operation` ConfigMap; an interrupted operation may leave it
behind. Remove that lock only after confirming its previous operator has stopped.

`down` stops nodes and retains PVCs. Use your cluster's backup/restore procedures
for stopped node volumes and shared blobs. To delete the deployment permanently:

```sh
./deploy/kubernetes.sh clean .kube-deployment --yes
```

This stops the nodes, deletes their dedicated namespace, and waits for its disks
to disappear. It requires volumes with a `Delete` reclaim policy; retained disks
need your cluster's explicit cleanup procedure. An interrupted cleanup can be
retried with the same command. Shared blobs are unchanged. Use a fresh deployment
directory, namespace, and blob storage for a new deployment after cleanup.

For a new Azure cluster, follow [the Azure walkthrough](Azure.md). It includes
the registry push, workload identity setup, first run and complete teardown.

For a new EKS cluster, follow [the AWS walkthrough](AWS.md). It uses the same
Kubernetes helper and console commands as Azure, with ECR, S3 and EBS.
