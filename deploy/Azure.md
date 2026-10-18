# Run Lean Cloud on Azure

Create a small AKS cluster, deploy the bundled application, and run the
log-processing example. All deployment commands below are inspectable scripts
in `deploy/`. They call Azure CLI, Docker, OpenTofu, and Kubernetes for you.
The cloud console remains an HTTP client for Lean Cloud workflows.

The application flow is the same as [local Docker](README.md#local-docker):
**build → configure → up → connect → run**. Azure adds the cluster setup and
registry publishing steps below.

Already have a cluster? Use the [existing Kubernetes instructions](README.md#existing-kubernetes-cluster).

## 1. Check tools and sign in

Run from the repository directory. Install the [local prerequisites](README.md#local-docker),
[Azure CLI](https://learn.microsoft.com/en-us/cli/azure/install-azure-cli),
[OpenTofu](https://opentofu.org/docs/intro/install/) (>= 1.10, < 2), `kubectl`, and
[Azure kubelogin](https://azure.github.io/kubelogin/install.html).

```sh
./deploy/azure.sh doctor
./deploy/azure.sh login YOUR_SUBSCRIPTION_NAME_OR_ID
```

`login` explicitly opens Azure's sign-in flow and selects your subscription.
Authentication stays with Azure CLI; the helpers do not collect credentials.
Other commands use that existing login and never initiate sign-in themselves.
Your account needs permission to create AKS, registry, storage, managed identities,
and role assignments. Regional VM quota and provider registration must allow them.

## 2. Configure and create the cluster

Replace `YOUR_PUBLIC_IPV4` with your administrator machine's public IPv4 address.
The `/32` restricts Kubernetes API access to that address. This helper does not
contact an IP lookup service. Use a fresh directory and a unique cluster name.

```sh
./deploy/azure.sh init .azure-infra --name azure-demo \
  --admin-cidr YOUR_PUBLIC_IPV4/32 --region northeurope --machines 1
./deploy/azure.sh show .azure-infra
./deploy/azure.sh plan .azure-infra
```

`init` writes `.azure-infra/azure.tfvars.json`; you can edit it before planning.
It uses the selected subscription and pins the latest non-preview Kubernetes
patch offered in the region. Use `--kubernetes-version` to select one yourself.
`./deploy/azure.sh help` lists the other configuration options.

The first plan binds this directory to the cluster name, subscription, region and
namespace. Use a fresh directory to change these. VM count, size and administrator
access settings remain editable through a new plan.

Review the plan, then apply it:

```sh
./deploy/azure.sh create .azure-infra
```

`create` applies the saved plan and saves the cluster credentials locally. If you
edit the configuration, run `plan` again before `create`. If saving cluster metadata
or retrieving credentials fails after provisioning succeeds, retry only
`./deploy/azure.sh credentials .azure-infra`. This refreshes metadata from OpenTofu
state and retrieves credentials without applying the plan again.

The default is **one ARM64 VM** (`Standard_D4ps_v6`), with no automatic scaling.
The application will run one scheduler and three workers on it. This is a small
development setup; VMs, disks, registry, storage, and networking incur charges
until removed. Keep this directory: it contains the state needed for cleanup.

## 3. Build and publish the application

```sh
./deploy/build.sh --platform linux/arm64 . lean-cloud-demo:dev
./deploy/azure.sh publish .azure-infra lean-cloud-demo:dev demo
```

The image contains the registered `log-summary` and `sum-squares` workflows.
`publish` authenticates Docker using your existing Azure session, tags the local
image for this cluster's registry, and pushes it. If uploading is interrupted,
rerun `publish`; no rebuild is needed. Use `linux/amd64` if you chose an x86 VM.

For your own application, replace the build command with its build script or
`./deploy/build.sh --platform linux/arm64 ../my-app my-app:dev`, then publish
that local image. See [application setup](README.md#your-application).

## 4. Configure and start the nodes

```sh
./deploy/azure.sh configure .azure-infra .azure-deployment demo 3
./deploy/kubernetes.sh show .azure-deployment
# Review .azure-deployment/deployment.json, storage.json, and resources.json.
./deploy/kubernetes.sh up .azure-deployment
./deploy/kubernetes.sh status .azure-deployment
```

`configure` writes files without changing the cluster. It resolves `demo` to an
immutable image digest and fills in the namespace, blob storage, workload
identity, and kubeconfig path. No manual JSON plumbing or environment exports
are needed. Use a fresh deployment directory.

The workers access Azure Blob Storage through workload identity; no storage key
is needed. Each node has its own SQLite disk. Keep both generated directories
private: they contain infrastructure state and, after `up`, deployment tokens.

For larger jobs, edit these settings **before the first `up`**:

| File | Setting | Meaning |
| --- | --- | --- |
| `.azure-infra/azure.tfvars.json` | `machines`, `machine_size` | VM count and size; rerun `plan` and `create` after edits |
| `.azure-infra/azure.tfvars.json` | `os_disk_size_gb` | VM disk for images and temporary workspaces; default 32 GiB |
| `.azure-deployment/deployment.json` | `workers` | Number of worker containers |
| `.azure-deployment/deployment.json` | `cpuMillis`, `memoryMiB` | CPU request and memory request/limit per node |
| `.azure-deployment/deployment.json` | `diskGiB` | Persistent disk per node for SQLite and application caches |
| `.azure-deployment/deployment.json` | `schedulerResources` | Optional smaller scheduler CPU/memory settings |
| `.azure-deployment/deployment.json` | `startupSeconds` | Startup wait; use 900 for LeanBuild toolchain downloads |

Worker count is independent of VM count. Kubernetes places the containers on the
available VMs. Ensure the requested CPU, memory, and disks fit your cluster.

## 5. Connect and run

Start the private tunnel and leave it running:

```sh
./deploy/kubernetes.sh connect .azure-deployment 8081
```

In a **second terminal**, open the console from the repository directory:

```sh
lake exe lean_cloud
```

At the `cloud>` prompt:

```text
connect azure-demo http://127.0.0.1:8081 --token-file .azure-deployment/client.token
programs
run log-summary --id my-logs
ps
watch my-logs
```

Press `q` to leave `watch`. Once the run is completed:

```text
result my-logs
```

Expected report: `files=16, errors=24`. The example creates its own sample input
blobs. Use a new `--id` for another run.

`127.0.0.1:8081` is the local end of the tunnel to the Azure scheduler. Its HTTP
port is not exposed to the public internet. If the tunnel closes or the scheduler
pod restarts, rerun the `connect` script. The console profile stays valid.

## 6. Stop, resize, or remove

After exiting the console and stopping the tunnel with Ctrl-C:

```sh
./deploy/kubernetes.sh down .azure-deployment  # stop nodes; keep data
./deploy/kubernetes.sh up .azure-deployment    # restart
./deploy/kubernetes.sh scale .azure-deployment 5  # change worker count
```

`scale` updates `workers` in deployment.json. Like local scaling, it stops old
nodes before starting replacements and preserves their disks. This changes
worker count, not Azure VM count. Choose a count that fits the cluster; the
command does not provision more machines. For new application code, use a fresh deployment
with separate state and blobs.

**Stopping the application does not stop Azure billing.** When finished, remove
the application and its disks, then review and apply infrastructure deletion:

```sh
./deploy/kubernetes.sh clean .azure-deployment --yes
./deploy/azure.sh destroy-plan .azure-infra
./deploy/azure.sh destroy .azure-infra
```

These commands permanently delete this example's workflows, outputs, and blobs.
`clean` waits for the node disks to be deleted while the storage controller is
still running. `destroy` removes the Azure resources, including shared blobs,
and checks that the resource group is gone. Keep the local directories until
cleanup succeeds. Never delete state files as a substitute for destroying resources.

If provisioning failed before any application was started, skip `clean` and use
`destroy-plan` and `destroy` to remove any resources already created.
