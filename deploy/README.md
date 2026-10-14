# Deploying Lean Cloud

The console is an HTTP client. These optional shell helpers build and deploy
nodes; you can inspect, edit, or replace them with your own tooling. An existing
Kubernetes cluster needs no cloud provisioning helper.

## Local Docker

Requires Docker (Compose and Buildx), `jq`, and `openssl`.
From the repository directory:

```sh
./deploy/build.sh . lean-cloud-demo:dev
./deploy/local.sh init .deployment lean-cloud-demo:dev development 3 8080
# Review .deployment/compose.json and .deployment/config.json.
./deploy/local.sh up .deployment
lake exe lean_cloud
```

Continue with [the log-processing example](#run-the-log-processing-example)
to submit and watch your first workflow.

The helper creates one scheduler, the specified workers, and local blob storage.
Each node hosts its HTTP inbox and embedded SQLite database. Submitting a run
uses these existing nodes. Only the scheduler port is published, on loopback.
Client and internal tokens are separate; the deployment directory is private.
Its runtime config is readable inside the container by the unprivileged worker.
The helper generates separate random client, mailbox, and blob credentials for
each deployment. The fixed values in `deploy/config.json` and `deploy/s3.json`
are used only by the repository's isolated Compose test fixture.

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

Expected output:

```text
files=16, errors=24
```

See the [workflow](../runtime/LeanCloudRuntime/Demo.lean) and
[console guide](../LeanCloud/Console.md). For a remote deployment, connect to its
scheduler endpoint instead; the workflow commands are the same.

## Your application

```sh
./deploy/new-app.sh ../my-app "$PWD"
# Edit ../my-app/Main.lean: register your CloudProgram values.
./deploy/build.sh ../my-app my-app:dev cloud_app "$PWD"
./deploy/local.sh init .my-app-deployment my-app:dev my-app 3 8081
./deploy/local.sh up .my-app-deployment
```

`Main.lean` delegates to `Application.main registry args`. The same executable
serves either a scheduler or a worker. `deploy/app/Dockerfile` is an ordinary
Buildx Dockerfile with explicit SDK and node source contexts. Building and
publishing for a remote architecture is a normal Docker operation:

```sh
docker buildx build --platform linux/arm64 --push \
  --build-context sdk="$PWD" --build-context node_assets="$PWD/deploy" \
  --build-arg LEAN_VERSION="$(sed 's|leanprover/lean4:v||' lean-toolchain)" \
  --build-arg APP_TARGET=cloud_app -f deploy/app/Dockerfile \
  -t YOUR_REGISTRY/cloud-app:VERSION ../my-app
```

Sign in to the registry yourself using its documented Docker/provider CLI flow.
Use the resulting registry digest (`IMAGE@sha256:...`) in Kubernetes.

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
./deploy/kubernetes.sh connect .kube-deployment
```

`connect` runs a foreground loopback port-forward and prints the console command.
Its optional final argument selects the local port, for example
`./deploy/kubernetes.sh connect .kube-deployment 8081` (default: 8080).
Keep it running in another terminal. If the scheduler pod restarts or the tunnel
disconnects, run `connect` again; saved CLI profiles still use the same address.
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
For AWS IRSA, set `eks.amazonaws.com/role-arn` and
`eks.amazonaws.com/sts-regional-endpoints: "true"` in serviceAccountAnnotations:

```json
{"provider":"s3","endpoint":"https://s3.eu-west-1.amazonaws.com","bucket":"YOUR_BUCKET","region":"eu-west-1","authentication":{"kind":"workload"},"provisioned":true}
```

An S3-compatible service can instead use `accessKey` and `secretKey` in the
private storage.json file. The bucket/container must already exist when marked
provisioned. Provider credentials stay in the nodes' workload identities.

To change worker count, edit deployment.json and run `up` again. The helper
stops all old pods and waits for deletion before any replacement starts. It
records PVC UIDs and rejects missing/replaced claims. Operations are serialized
with the `cloud-operation` ConfigMap; an interrupted operation may leave it
behind. Remove that lock only after confirming its previous operator has stopped.

`down` stops nodes and retains PVCs. Use your cluster's backup/restore procedures
for stopped node volumes and shared blobs. To delete the deployment permanently,
stop it, then explicitly delete its dedicated namespace. Deleting it destroys
SQLite state; blob cleanup is a separate operation owned by your storage tooling.

## Optional Azure / AWS infrastructure

Login is always external: `az login` or `aws login --profile lean-cloud`.
The console never performs cloud login or reads provider credential stores.
OpenTofu modules live in `deploy/infrastructure/{azure,aws}/main.tf`.
They provision the cluster, registry, blob storage and workload identities;
Kubernetes deployment remains a separate step.

```sh
cp deploy/infrastructure/azure/terraform.tfvars.example.json azure.tfvars.json
# Supply subscription ID, region, a supported Kubernetes version and your IP CIDR.
./deploy/infrastructure.sh plan azure .azure-infra azure.tfvars.json
# Review the complete OpenTofu plan.
./deploy/infrastructure.sh create .azure-infra
./deploy/kubeconfig.sh .azure-infra
export KUBECONFIG="$PWD/.azure-infra/kubeconfig"
```

For AWS, use the AWS example and `plan aws`. A suitable account must permit EKS
and IAM OIDC; AWS live deployment remains unverified in our development account.
The wrapper does not install tools, log in, choose accounts, or discover your IP.
`create` applies the exact saved plan. `cloud.json` contains the resulting
registry and storage identity values for your Kubernetes deployment files.

For teardown, stop the workload and delete its dedicated namespace first. Wait
for workload volumes to be released while the cluster's storage controller still
runs. Then review and apply infrastructure deletion:

```sh
./deploy/infrastructure.sh destroy-plan .azure-infra
./deploy/infrastructure.sh destroy .azure-infra
```

Keep the OpenTofu state directory until cleanup finishes. Never delete state to
"clean" a cluster: that leaves billable cloud resources behind. Existing state
created by older CLI versions is not migrated or deleted by these helpers.
