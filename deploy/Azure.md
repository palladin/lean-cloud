# Run Lean Cloud on Azure

This walkthrough creates a small AKS cluster, deploys the bundled application,
and runs the log-processing example. The console connects to the scheduler over
HTTP through a local Kubernetes port-forward. No public application endpoint or
DNS setup is needed.

The shell helpers are optional and inspectable. If you already have Kubernetes,
start with [existing-cluster deployment](README.md#existing-kubernetes-cluster).
The console itself only manages Lean Cloud workflows.

## 1. Tools and login

Use a shell in the repository directory. You need the [local prerequisites](README.md#local-docker),
plus [Azure CLI](https://learn.microsoft.com/en-us/cli/azure/install-azure-cli),
[OpenTofu](https://opentofu.org/docs/intro/install/) (>= 1.10, < 2), `kubectl`, and
[Azure kubelogin](https://azure.github.io/kubelogin/install.html).

Sign in yourself and select the subscription that should pay for the test:

```sh
az login
az account set --subscription YOUR_SUBSCRIPTION_NAME_OR_ID
az account show --query '{name:name,id:id}' --output table
lake build lean_cloud
```

Your account needs permission to create AKS, a registry, storage, managed
identities and role assignments. The helper uses your existing Azure CLI login;
it does not sign you in or install software. Azure provider registration and VM
quota must already allow these resources in your chosen region.

This example uses **one ARM64 VM** (`Standard_D4ps_v6`) with one scheduler and
three worker pods. Workers are processes in containers, not separate VMs. It is
a development setup, not a highly available cluster. Azure charges for the VM,
disks, registry, storage and networking until you remove them in step 7.
`os_disk_size_gb` sets each VM's OS disk (default 32 GiB), which also holds
container images and temporary workspaces. Increase it for large build jobs.
The separate `diskGiB` deployment setting controls each node's persistent data
volume, including SQLite and any application cache.

## 2. Configure and provision

Use fresh `.azure-infra` and `.azure-deployment` directories. Set your public
administrator IPv4 address below; `/32` restricts Kubernetes API access to that
address. Use a unique cluster name if `azure-demo` already exists.

```sh
cloud_subscription=$(az account show --query id --output tsv)
cloud_region=northeurope
cloud_admin_cidr='YOUR_PUBLIC_IPV4/32'
az aks get-versions --location "$cloud_region" --output table
```

Choose a supported non-preview Kubernetes version from that list. The example
uses `1.35`; change it if your region no longer offers that version. Create the
configuration from the supplied template:

```sh
jq --arg subscription "$cloud_subscription" \
   --arg region "$cloud_region" --arg cidr "$cloud_admin_cidr" \
   '.name="azure-demo" | .subscription=$subscription | .region=$region |
    .machines=1 | .kubernetes_version="1.35" | .administrator_cidrs=[$cidr]' \
   deploy/infrastructure/azure/terraform.tfvars.example.json > azure.tfvars.json
cat azure.tfvars.json
./deploy/infrastructure.sh plan azure .azure-infra azure.tfvars.json
```

Review the plan before applying it. `plan` creates no cloud resources. `create`
applies that exact saved plan; if you edit the configuration, run `plan` again.

```sh
./deploy/infrastructure.sh create .azure-infra
./deploy/kubeconfig.sh .azure-infra
export KUBECONFIG="$PWD/.azure-infra/kubeconfig"
kubectl get nodes
```

Provisioning takes several minutes. The resulting registry and storage details
are in `.azure-infra/cloud.json`; `azure.tfvars.json` remains your input.
If Kubernetes initially reports `Forbidden`, allow time for the new Azure role
assignment to propagate and retry `kubectl get nodes`.

## 3. Publish the application

The repository's Dockerfile includes the registered `log-summary` and
`sum-squares` workflows. Sign Docker in to the new registry using your Azure
session, then build and push its ARM64 image:

```sh
cloud_registry=$(jq -r .registryName .azure-infra/cloud.json)
cloud_repository=$(jq -r .repository .azure-infra/cloud.json)
az acr login --name "$cloud_registry"
docker buildx build --platform linux/arm64 --target worker --load \
  --build-arg LEAN_VERSION="$(sed 's|leanprover/lean4:v||' lean-toolchain)" \
  --tag "$cloud_repository:demo" .
docker push "$cloud_repository:demo"
az acr repository show --name "$cloud_registry" --image cloud-app:demo \
  --query digest --output tsv > .azure-infra/image-digest.txt
```

Use `linux/amd64` instead if you selected an x86 VM. For your own application,
use the [application Dockerfile](README.md#your-application) with `--load`
instead of `--push` and tag it as `"$cloud_repository:demo"`, then run the push
and digest commands above. The next step
uses the registry's **digest**, so worker restarts keep exactly the same code.

Building and publishing are separate so an interrupted upload can be retried
with `docker push` without rebuilding. Only continue after the push and digest
lookup succeed. For repeated upload timeouts, see
[Azure registry network troubleshooting](https://learn.microsoft.com/en-us/azure/container-registry/container-registry-troubleshoot-access).

## 4. Configure and start the nodes

Generate the deployment files from the infrastructure outputs:

```sh
mkdir -m 700 .azure-deployment
cloud_context=$(kubectl config current-context)
cloud_digest=$(cat .azure-infra/image-digest.txt)
jq --slurpfile infra .azure-infra/cloud.json \
   --slurpfile vars .azure-infra/terraform.tfvars.json \
   --arg context "$cloud_context" --arg digest "$cloud_digest" \
   '.name=$infra[0].name | .context=$context | .namespace=$vars[0].namespace |
    .image=($infra[0].repository + "@" + $digest) | .workers=3 |
    .storageClass=$infra[0].storageClass |
    .serviceAccountAnnotations={
      "azure.workload.identity/client-id": $infra[0].storage.clientId,
      "azure.workload.identity/tenant-id": $infra[0].storage.tenantId} |
    .podLabels={"azure.workload.identity/use":"true"}' \
   deploy/kubernetes/deployment.example.json > .azure-deployment/deployment.json
jq '.storage | {provider:"azure",
    endpoint:("https://" + .account + ".blob.core.windows.net"),
    container:.container, authentication:{kind:"workload"}}' \
   .azure-infra/cloud.json > .azure-deployment/storage.json

./deploy/kubernetes.sh render .azure-deployment
# Review .azure-deployment/deployment.json, storage.json and resources.json.
./deploy/kubernetes.sh up .azure-deployment
cloud_namespace=$(jq -r .namespace .azure-deployment/deployment.json)
kubectl --namespace "$cloud_namespace" get pods
```

The namespace must match the infrastructure configuration: Azure workload
identity grants blob access to `cloud-node` in that namespace. The generated
annotations and pod label enable this identity; no storage access key is needed.
See [Azure's workload identity documentation](https://learn.microsoft.com/en-us/azure/aks/workload-identity-deploy-cluster).

Each node has its own SQLite disk. Replay records and user files share the Azure
blob container. Keep the generated directory private: `up` writes separate client
and internal tokens there. Do not commit it or the infrastructure state.

## 5. Connect and run the example

In the same shell, start the tunnel and leave it running. Port 8081 avoids the
local Docker example's port 8080:

```sh
./deploy/kubernetes.sh connect .azure-deployment 8081
```

In a **second terminal**, change to the repository directory and open the console:

```sh
lake exe lean_cloud
```

At the `cloud>` prompt:

```text
connect azure-demo http://127.0.0.1:8081 --token-file .azure-deployment/client.token
programs
run log-summary --id azure-logs
ps
watch azure-logs
```

`watch` shows branches, source lines and workers. Press `q` to return to the
prompt. Once `ps` reports `completed`, read the output blob:

```text
result azure-logs
```

Expected report:

```text
files=16, errors=24
```

These are the same workflow commands used locally. The example creates its own
sample input blobs. Use a new `--id` for another run. If the tunnel closes or the
scheduler pod restarts, rerun the shell `connect` helper; the console profile
continues to use the same local address.

## 6. Stop or change worker count

Type `quit` in the console, then stop the tunnel with Ctrl-C. In your original
shell, these commands stop and restart the application while retaining data:

```sh
./deploy/kubernetes.sh down .azure-deployment
./deploy/kubernetes.sh up .azure-deployment
```

To change worker count, edit `workers` in `.azure-deployment/deployment.json`
and run `up` again. The helper stops old nodes before replacements start and
preserves their volumes. This does not change the number of Azure VMs; workers
must fit the cluster's available capacity. Use a fresh deployment for a new
application image.

**`down` does not stop Azure billing.** Use the following cleanup when finished.

## 7. Remove the test deployment and infrastructure

The following permanently deletes this example's workflows, outputs and blobs.
Stop the tunnel first. In the original shell, remove the application and its
disks while the cluster's storage controller is still running:

```sh
export KUBECONFIG="$PWD/.azure-infra/kubeconfig"
cloud_namespace=$(jq -r .namespace .azure-deployment/deployment.json)
./deploy/kubernetes.sh down .azure-deployment
kubectl get pv --output json | jq -r --arg ns "$cloud_namespace" \
  '.items[] | select(.spec.claimRef.namespace == $ns) | .metadata.name' \
  > .azure-deployment/volumes.txt
kubectl delete namespace "$cloud_namespace" --wait=true
while IFS= read -r cloud_volume; do
  kubectl wait --for=delete "pv/$cloud_volume" --timeout=300s
done < .azure-deployment/volumes.txt
```

Review and apply deletion of the Azure resources:

```sh
./deploy/infrastructure.sh destroy-plan .azure-infra
./deploy/infrastructure.sh destroy .azure-infra
az group exists --subscription "$(jq -r .subscription .azure-infra/terraform.tfvars.json)" \
  --name "$(jq -r .resourceGroup .azure-infra/cloud.json)"
```

The final command should print `false`. Keep the state directory until deletion
has finished. If provisioning failed before the application was deployed, skip
the application cleanup and use `destroy-plan` and `destroy` to remove any
resources already created. Never delete the state directory as a substitute for
destroying infrastructure.
