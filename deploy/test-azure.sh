#!/usr/bin/env bash
# Exercise the documented workflow without an account, cloud resources, or Docker.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$root"
work=$(mktemp -d)
work=$(cd "$work" && pwd -P)
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin"
export HELPER_AZURE_WORK="$work"
cat > "$work/bin/az" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf 'az %s\n' "$*" >> "$HELPER_AZURE_WORK/calls"
case "$*" in
  'login --output none'|'account set --subscription '*) ;;
  'account show '*'--output table') printf 'test-subscription\n' ;;
  'account show '*) printf '00000000-0000-0000-0000-000000000001\n' ;;
  'aks get-versions '*) printf '{"values":[{"isPreview":false,"patchVersions":{"1.9.9":{},"1.35.2":{},"1.35.10":{}}},{"isPreview":true,"patchVersions":{"1.36.0":{}}}]}' ;;
  'aks get-credentials '*)
    while [[ $1 != --file ]]; do shift; done
    printf 'test credentials\n' > "$2" ;;
  'acr login '*) ;;
  'acr repository show '*)
    if [[ ${HELPER_BAD_DIGEST:-0} == 1 ]]; then echo invalid; else printf 'sha256:%064d\n' 1; fi ;;
  'group exists '*) printf 'false\n' ;;
  *) echo "Unexpected Azure action: $*" >&2; exit 1 ;;
esac
MOCK
cat > "$work/bin/tofu" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf 'tofu %s\n' "$*" >> "$HELPER_AZURE_WORK/calls"
directory=${1#-chdir=}; shift
case "$*" in
  init) ;;
  'plan -out=provision.tfplan.pending') touch "$directory/provision.tfplan.pending" ;;
  'plan -destroy -out=destroy.tfplan.pending') touch "$directory/destroy.tfplan.pending" ;;
  'apply provision.tfplan') [[ -f "$directory/provision.tfplan" ]] ;;
  'apply destroy.tfplan') [[ -f "$directory/destroy.tfplan" ]] ;;
  'output -json cloud') cat "$HELPER_AZURE_WORK/cloud.json" ;;
  *) echo "Unexpected OpenTofu action: $*" >&2; exit 1 ;;
esac
MOCK
cat > "$work/bin/kubectl" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf 'kubectl %s\n' "$*" >> "$HELPER_AZURE_WORK/calls"
case "$*" in
  '--kubeconfig '*' config current-context') printf 'azure-demo\n' ;;
  *' get nodes -o wide'|*' get pods -l lean-cloud/deployment=azure-demo -o wide') ;;
  *' port-forward --address 127.0.0.1 service/cloud-api 8081:8080') ;;
  *) echo "Unexpected Kubernetes action: $*" >&2; exit 1 ;;
esac
MOCK
cat > "$work/bin/docker" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf 'docker %s\n' "$*" >> "$HELPER_AZURE_WORK/calls"
case "$*" in
  info|'buildx version'|'buildx build '*|'tag '*) ;;
  'push '*) [[ ${HELPER_PUSH_FAIL:-0} == 0 ]] ;;
  *) echo "Unexpected Docker action: $*" >&2; exit 1 ;;
esac
MOCK
cat > "$work/bin/kubelogin" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf 'kubelogin %s\n' "$*" >> "$HELPER_AZURE_WORK/calls"
[[ $1 == convert-kubeconfig && ${!#} == azurecli ]]
MOCK
chmod +x "$work/bin/"*
export PATH="$work/bin:$PATH"
cat > "$work/cloud.json" <<'JSON'
{"provider":"azure","name":"azure-demo","region":"northeurope",
 "registry":"test.azurecr.io","registryName":"test","repository":"test.azurecr.io/cloud-app",
 "resourceGroup":"lean-cloud-azure-demo","storageClass":"managed-csi",
 "storage":{"provider":"azure","account":"teststorage","container":"cloud","clientId":"test-client","tenantId":"test-tenant"}}
JSON
infra="$work/azure infra"; deployment="$work/azure deployment"
bash deploy/azure.sh doctor
bash deploy/azure.sh login test-subscription
: > "$work/calls"
bash deploy/azure.sh init "$infra" --name azure-demo --admin-cidr 192.0.2.1/32
jq -e '.machines==1 and .kubernetes_version=="1.35.10" and .administrator_cidrs==["192.0.2.1/32"] and .machine_size=="Standard_D4ps_v6"' "$infra/azure.tfvars.json" >/dev/null
if grep -q 'apply\|az login' "$work/calls"; then echo 'init provisioned or signed in'; exit 1; fi
bash deploy/azure.sh show "$infra" > "$work/shown.json"
cmp "$infra/azure.tfvars.json" "$work/shown.json"
if bash deploy/azure.sh init "$infra" --name other --admin-cidr 192.0.2.1/32 2>/dev/null; then echo 'Overwrote infrastructure config'; exit 1; fi
for invalid in 999.0.0.1/32 192.0.2.1/0 192.0.2.1; do
  if bash deploy/azure.sh init "$work/invalid" --name invalid --admin-cidr "$invalid" 2>/dev/null; then echo 'Accepted invalid administrator address'; exit 1; fi
done
[[ ! -e "$work/invalid" ]]
bash deploy/azure.sh init "$work/custom" --name custom --admin-cidr 192.0.2.2/32 \
  --subscription another --region westeurope --machines 2 --machine-size Standard_D4s_v5 \
  --os-disk-gib 128 --kubernetes-version 1.35 --namespace custom
jq -e '.machines==2 and .os_disk_size_gb==128 and .namespace=="custom" and .region=="westeurope" and .machine_size=="Standard_D4s_v5" and .kubernetes_version=="1.35"' "$work/custom/azure.tfvars.json" >/dev/null
bash deploy/azure.sh plan "$infra"
cmp "$infra/azure.tfvars.json" "$infra/terraform.tfvars.json"
# An Azure command must not apply a plan from another provider's state directory.
printf 'aws\n' > "$infra/provider"
if bash deploy/azure.sh create "$infra" 2>/dev/null; then echo 'Applied another provider plan'; exit 1; fi
printf 'azure\n' > "$infra/provider"
# create applies the exact saved plan, not edits made after planning.
jq '.machines=2' "$infra/azure.tfvars.json" > "$work/edited.json"
mv "$work/edited.json" "$infra/azure.tfvars.json"
bash deploy/azure.sh create "$infra"
jq -e '.machines==1' "$infra/terraform.tfvars.json" >/dev/null
[[ -s "$infra/kubeconfig" ]]
grep -Fq ' -l azurecli' "$work/calls"
cp "$infra/terraform.tfvars.json" "$work/saved-vars.json"
cp "$infra/azure.tfvars.json" "$work/editable-vars.json"
for change in '.name="another-cluster"' '.subscription="00000000-0000-0000-0000-000000000002"' '.region="westeurope"' '.namespace="another-namespace"'; do
  jq "$change" "$work/editable-vars.json" > "$infra/azure.tfvars.json"
  : > "$work/calls"
  if bash deploy/azure.sh plan "$infra" > "$work/result" 2>&1; then echo 'Changed the identity of existing infrastructure'; exit 1; fi
  grep -Fq 'Use a fresh infrastructure directory' "$work/result"
  cmp "$work/saved-vars.json" "$infra/terraform.tfvars.json"
  if grep -q '^tofu ' "$work/calls"; then echo 'Contacted provider after identity change'; exit 1; fi
done
cp "$work/editable-vars.json" "$infra/azure.tfvars.json"
bash deploy/azure.sh plan "$infra"
jq -e '.machines==2 and .name=="azure-demo"' "$infra/terraform.tfvars.json" >/dev/null
# Credential recovery refreshes missing outputs from state, without reapplying.
rm "$infra/cloud.json"
: > "$work/calls"
bash deploy/azure.sh credentials "$infra"
cmp "$work/cloud.json" "$infra/cloud.json"
if grep -q 'apply' "$work/calls"; then echo 'Reapplied resources to recover credentials'; exit 1; fi
bash deploy/build.sh --platform linux/arm64 . lean-cloud-demo:dev
grep -Fq 'docker buildx build --load --platform linux/arm64 --target worker' "$work/calls"
bash deploy/build.sh --platform linux/amd64 Applications/LeanBuild app:dev
grep -Fq 'docker buildx build --load --platform linux/amd64 --build-context' "$work/calls"
if bash deploy/build.sh --platform invalid . app:dev 2>/dev/null; then echo 'Accepted invalid platform'; exit 1; fi
if HELPER_PUSH_FAIL=1 bash deploy/azure.sh publish "$infra" lean-cloud-demo:dev demo; then echo 'Ignored push failure'; exit 1; fi
bash deploy/azure.sh publish "$infra" lean-cloud-demo:dev demo
grep -Fq 'docker tag lean-cloud-demo:dev test.azurecr.io/cloud-app:demo' "$work/calls"
if HELPER_BAD_DIGEST=1 bash deploy/azure.sh configure "$infra" "$deployment" demo 3 2>/dev/null; then echo 'Accepted invalid registry digest'; exit 1; fi
[[ ! -e "$deployment" ]]
bash deploy/azure.sh configure "$infra" "$deployment" demo 3
jq -e --arg kubeconfig "$infra/kubeconfig" '.workers==3 and .kubeconfig==$kubeconfig and
  .namespace=="lean-cloud" and .context=="azure-demo" and
  .image==("test.azurecr.io/cloud-app@sha256:" + ("0"*63) + "1") and
  .serviceAccountAnnotations["azure.workload.identity/client-id"]=="test-client" and
  .podLabels["azure.workload.identity/use"]=="true"' "$deployment/deployment.json" >/dev/null
jq -e '.endpoint=="https://teststorage.blob.core.windows.net" and .authentication.kind=="workload"' "$deployment/storage.json" >/dev/null
jq -e '[.items[]|select(.kind=="StatefulSet")]|length==4' "$deployment/resources.json" >/dev/null
grep -Fxq '*' "$deployment/.gitignore"
if bash deploy/azure.sh configure "$infra" "$deployment" other 1 2>/dev/null; then echo 'Replaced existing deployment'; exit 1; fi
# The pinned kubeconfig is used even in a different shell/context.
export KUBECONFIG="$work/unrelated"
bash deploy/kubernetes.sh status "$deployment"
bash deploy/kubernetes.sh connect "$deployment" 8081
grep -Fq -- "--kubeconfig $infra/kubeconfig --request-timeout=30s get nodes" "$work/calls"
grep -Fq -- "--kubeconfig $infra/kubeconfig port-forward" "$work/calls"
if grep -q '^az login' "$work/calls"; then echo 'Signed in implicitly'; exit 1; fi
bash deploy/azure.sh destroy-plan "$infra"
bash deploy/azure.sh destroy "$infra"
grep -Fq 'group exists --subscription 00000000-0000-0000-0000-000000000001 --name lean-cloud-azure-demo' "$work/calls"
printf 'Azure command workflow contracts passed.\n'
