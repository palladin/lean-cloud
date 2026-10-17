#!/usr/bin/env bash
# Inspectable Azure workflow. Login is explicit; no tools are installed.
set -euo pipefail
assets=$(cd "$(dirname "$0")" && pwd -P)
source "$assets/common.sh"
usage() {
  cat <<'USAGE'
Usage: deploy/azure.sh COMMAND ...
  doctor
  login SUBSCRIPTION
  init INFRA_DIR --name NAME --admin-cidr IPV4/32 [OPTIONS]
    --subscription NAME_OR_ID  (default: current Azure subscription)
    --region REGION           (default: northeurope)
    --machines N              (default: 1)
    --machine-size SIZE       (default: Standard_D4ps_v6, ARM64)
    --os-disk-gib N           (default: 32)
    --kubernetes-version V    (default: latest non-preview version in region)
    --namespace NAME          (default: lean-cloud)
  show|plan|create|credentials|destroy-plan|destroy INFRA_DIR
  publish INFRA_DIR LOCAL_IMAGE TAG
  configure INFRA_DIR DEPLOYMENT_DIR TAG [WORKERS]   (default: 3)

Edit INFRA_DIR/azure.tfvars.json before plan. Review the plan before create.
configure writes files only; use deploy/kubernetes.sh up to start the nodes.
USAGE
}
command=${1:-help}
if [[ $command == help || $command == --help ]]; then usage; exit; fi
if [[ $command == doctor ]]; then
  [[ $# == 1 ]] || fail 'Usage: deploy/azure.sh doctor'
  for tool in az tofu kubectl kubelogin docker jq openssl shasum; do need "$tool"; printf '[ok] %s\n' "$tool"; done
  docker buildx version >/dev/null
  docker info >/dev/null
  printf 'Tools and Docker engine are available. Login and provisioning permissions are checked separately.\n'
  exit
fi
need jq; need az
if [[ $command == login ]]; then
  [[ $# == 2 ]] || fail 'Usage: deploy/azure.sh login SUBSCRIPTION'
  az login --output none
  az account set --subscription "$2"
  az account show --query '{name:name,id:id}' --output table
  exit
fi
if [[ $command == init ]]; then
  [[ $# -ge 2 ]] || fail 'Usage: deploy/azure.sh init INFRA_DIR --name NAME --admin-cidr IPV4/32 [OPTIONS]'
  directory=$2; shift 2
  [[ ! -e "$directory" ]] || fail 'Destination already exists; edit its azure.tfvars.json instead.'
  name=; cidr=; subscription=; region=northeurope; machines=1
  machine_size=Standard_D4ps_v6; disk=32; version=; namespace=lean-cloud
  while [[ $# -gt 0 ]]; do
    [[ $# -ge 2 ]] || fail "Missing value for $1"
    case "$1" in
      --name) name=$2 ;; --admin-cidr) cidr=$2 ;; --subscription) subscription=$2 ;;
      --region) region=$2 ;; --machines) machines=$2 ;; --machine-size) machine_size=$2 ;;
      --os-disk-gib) disk=$2 ;; --kubernetes-version) version=$2 ;; --namespace) namespace=$2 ;;
      *) fail "Unknown option: $1" ;;
    esac
    shift 2
  done
  identifier "$name"; identifier "$namespace"; number "$machines"; number "$disk"
  (( machines > 0 && disk >= 32 )) || fail 'Use at least one machine and an OS disk of at least 32 GiB'
  jq -en --arg cidr "$cidr" '$cidr | test("^([0-9]{1,3}\\.){3}[0-9]{1,3}/32$") and
    (split("/")[0] | split(".") | all(tonumber <= 255))' >/dev/null || fail 'Supply your public administrator IPv4 address with /32'
  account_options=(account show)
  [[ -z "$subscription" ]] || account_options+=(--subscription "$subscription")
  subscription=$(az "${account_options[@]}" --query id --output tsv)
  [[ -n "$subscription" ]] || fail 'No Azure subscription selected. Run deploy/azure.sh login first.'
  if [[ -z "$version" ]]; then
    version=$(az aks get-versions --subscription "$subscription" --location "$region" --output json |
      jq -er '[.values[] | select(.isPreview!=true) | .patchVersions | keys[] |
        select(test("^[0-9]+\\.[0-9]+\\.[0-9]+$"))] | sort_by(split(".")|map(tonumber)) | last // empty')
  fi
  [[ "$version" =~ ^[0-9]+\.[0-9]+(\.[0-9]+)?$ ]] || fail 'Expected a stable Kubernetes version'
  mkdir -p "$directory"; directory=$(absolute_dir "$directory"); private_dir "$directory"
  jq -n --arg name "$name" --arg subscription "$subscription" --arg region "$region" \
    --arg cidr "$cidr" --arg machine "$machine_size" --arg version "$version" --arg namespace "$namespace" \
    --argjson machines "$machines" --argjson disk "$disk" \
    '{name:$name,subscription:$subscription,region:$region,machines:$machines,machine_size:$machine,
      os_disk_size_gb:$disk,kubernetes_version:$version,administrator_cidrs:[$cidr],namespace:$namespace}' \
    > "$directory/azure.tfvars.json"
  printf 'Created %s/azure.tfvars.json. No cloud resources were created.\n' "$directory"
  jq . "$directory/azure.tfvars.json"
  exit
fi
case "$command" in
  show|plan|create|credentials|destroy-plan|destroy)
    [[ $# == 2 ]] || fail "Usage: deploy/azure.sh $command INFRA_DIR"
    infra=$(absolute_dir "$2")
    if [[ $command != show && $command != plan ]]; then
      [[ -f "$infra/provider" && $(cat "$infra/provider") == azure ]] || fail 'Expected an Azure infrastructure state directory'
    fi
    case "$command" in
      show) jq . "$infra/azure.tfvars.json" ;;
      plan) bash "$assets/infrastructure.sh" plan azure "$infra" "$infra/azure.tfvars.json" ;;
      create)
        bash "$assets/infrastructure.sh" create "$infra"
        bash "$assets/kubeconfig.sh" "$infra" ;;
      credentials) bash "$assets/kubeconfig.sh" "$infra" ;;
      destroy-plan) bash "$assets/infrastructure.sh" destroy-plan "$infra" ;;
      destroy)
        bash "$assets/infrastructure.sh" destroy "$infra"
        exists=$(az group exists --subscription "$(jq -er .subscription "$infra/terraform.tfvars.json")" \
          --name "lean-cloud-$(jq -er .name "$infra/terraform.tfvars.json")")
        [[ "$exists" == false ]] || fail 'Azure still reports the resource group; check cleanup before removing local state.'
        printf 'Azure resource group removed.\n' ;;
    esac
    exit ;;
  publish) [[ $# == 4 ]] || fail 'Usage: deploy/azure.sh publish INFRA_DIR LOCAL_IMAGE TAG' ;;
  configure) [[ $# -ge 4 && $# -le 5 ]] || fail 'Usage: deploy/azure.sh configure INFRA_DIR DEPLOYMENT_DIR TAG [WORKERS]' ;;
  *) usage; exit 1 ;;
esac
infra=$(absolute_dir "$2"); tag=$4
[[ "$tag" =~ ^[a-zA-Z0-9_][a-zA-Z0-9_.-]{0,127}$ ]] || fail 'Expected an image tag, for example demo'
cloud="$infra/cloud.json"; vars="$infra/terraform.tfvars.json"
jq -e '.provider=="azure" and .storage.provider=="azure"' "$cloud" >/dev/null || fail 'Expected Azure infrastructure outputs'
registry=$(jq -er .registry "$cloud"); repository=$(jq -er .repository "$cloud")
[[ "$repository" == "$registry/"* ]] || fail 'Image repository does not belong to the infrastructure registry'
subscription=$(jq -er .subscription "$vars"); registry_name=$(jq -er .registryName "$cloud")
if [[ "$command" == publish ]]; then
  need docker
  az acr login --subscription "$subscription" --name "$registry_name"
  docker tag "$3" "$repository:$tag"
  docker push "$repository:$tag"
  printf 'Published %s:%s. Use configure to pin this image and prepare the deployment.\n' "$repository" "$tag"
  exit
fi
need kubectl
directory=$3; workers=${5:-3}
number "$workers"
[[ ! -e "$directory" ]] || fail 'Destination already exists; use a fresh deployment directory.'
name=$(jq -er .name "$cloud"); namespace=$(jq -er .namespace "$vars")
identifier "$name"; identifier "$namespace"
[[ -s "$infra/kubeconfig" ]] || fail 'Run deploy/azure.sh credentials for this infrastructure first.'
context=$(kubectl --kubeconfig "$infra/kubeconfig" config current-context)
[[ -n "$context" ]] || fail 'Kubeconfig has no current context'
# Resolve a mutable tag once; replay must always run the same application code.
digest=$(az acr repository show --subscription "$subscription" \
  --name "$registry_name" --image "${repository#"$registry/"}:$tag" \
  --query digest --output tsv)
[[ "$digest" =~ ^sha256:[a-f0-9]{64}$ ]] || fail 'Registry returned no valid image digest. Push the image first.'
mkdir -p "$directory"; directory=$(absolute_dir "$directory"); private_dir "$directory"
jq --slurpfile infra "$cloud" --arg context "$context" --arg namespace "$namespace" \
  --arg kubeconfig "$infra/kubeconfig" --arg digest "$digest" --argjson workers "$workers" '
  $infra[0] as $i |
  .name=$i.name | .context=$context | .kubeconfig=$kubeconfig | .namespace=$namespace |
  .image=($i.repository + "@" + $digest) | .workers=$workers |
  .storageClass=$i.storageClass |
  .serviceAccountAnnotations={
    "azure.workload.identity/client-id": $i.storage.clientId,
    "azure.workload.identity/tenant-id": $i.storage.tenantId} |
  .podLabels={"azure.workload.identity/use":"true"}
  ' "$assets/kubernetes/deployment.example.json" > "$directory/deployment.json"
jq '.storage | {provider:"azure",endpoint:("https://" + .account + ".blob.core.windows.net"),
  container:.container,authentication:{kind:"workload"}}' "$cloud" > "$directory/storage.json"
bash "$assets/kubernetes.sh" render "$directory"
printf 'Created %s with %s workers. No cloud resources were changed.\n' "$directory" "$workers"
printf 'Review deployment.json, storage.json and resources.json before starting.\n'
printf 'Next: deploy/kubernetes.sh up "%s"\n' "$directory"
