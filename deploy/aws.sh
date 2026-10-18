#!/usr/bin/env bash
# Inspectable AWS workflow. Authentication is explicit and stays with AWS CLI.
set -euo pipefail
assets=$(cd "$(dirname "$0")" && pwd -P)
source "$assets/common.sh"
usage() {
  cat <<'USAGE'
Usage: deploy/aws.sh COMMAND ...
  doctor
  login PROFILE [--region REGION] [--sso | --remote]
  init INFRA_DIR --name NAME --admin-cidr IPV4/32 [OPTIONS]
    --profile PROFILE          (default: lean-cloud)
    --account ACCOUNT_ID       (default: signed-in account; checked if supplied)
    --region REGION            (default: profile region; required if unset)
    --machines N               (default: 1)
    --machine-size SIZE        (default: m7g.large, ARM64)
    --os-disk-gib N            (default: 32)
    --worker-zone ZONE         (default: first zone offering the machine size)
    --kubernetes-version V     (default: latest version in standard support)
    --namespace NAME           (default: lean-cloud)
  show|plan|create|credentials|storage|destroy-plan|destroy INFRA_DIR
  publish INFRA_DIR LOCAL_IMAGE TAG
  configure INFRA_DIR DEPLOYMENT_DIR TAG [WORKERS]   (default: 3)

Edit INFRA_DIR/aws.tfvars.json before plan. Review the plan before create.
create also prepares cluster credentials and the EBS StorageClass; credentials
and storage can be retried separately. configure writes files only.
Use deploy/kubernetes.sh for up, status, connect, scale, down and clean.
USAGE
}
require_login_version() {
  local version
  version=$(aws --version)
  [[ "$version" =~ ^aws-cli/2\.([0-9]+)\. ]] && (( BASH_REMATCH[1] >= 32 )) ||
    fail 'Install AWS CLI v2.32.0 or newer for browser login'
}
command=${1:-help}
if [[ $command == help || $command == --help ]]; then usage; exit; fi
if [[ $command == doctor ]]; then
  [[ $# == 1 ]] || fail 'Usage: deploy/aws.sh doctor'
  for tool in aws tofu kubectl docker jq openssl shasum; do need "$tool"; printf '[ok] %s\n' "$tool"; done
  require_login_version
  docker buildx version >/dev/null
  docker info >/dev/null
  printf 'Tools and Docker engine are available. Login, account permissions and quota are checked separately.\n'
  exit
fi
need jq; need aws
export AWS_PAGER=""
valid_region() { [[ "$1" =~ ^(af|ap|ca|eu|il|me|mx|sa|us)-[a-z]+-[0-9]+$ ]] || fail 'Expected a commercial AWS region, for example eu-west-1'; }
valid_profile() { [[ "$1" =~ ^[a-zA-Z0-9_.-]+$ ]] || fail 'Use an AWS profile name containing letters, numbers, dots, underscores or dashes'; }
if [[ $command == login ]]; then
  [[ $# -ge 2 ]] || fail 'Usage: deploy/aws.sh login PROFILE [--region REGION] [--sso | --remote]'
  profile=$2; region=; sso=false; remote=false; shift 2
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --region) [[ $# -ge 2 ]] || fail 'Missing region'; region=$2; shift 2 ;;
      --sso) sso=true; shift ;;
      --remote) remote=true; shift ;;
      *) fail "Unknown login option: $1" ;;
    esac
  done
  valid_profile "$profile"
  [[ -n "$region" ]] || region=$(aws configure get region --profile "$profile" || true)
  [[ -n "$region" ]] || fail "Supply --region or configure a region in the AWS profile"
  valid_region "$region"
  if $sso; then
    $remote && fail 'Choose either --sso or --remote'
    aws sso login --profile "$profile" --region "$region"
  else
    require_login_version
    login_options=(login --profile "$profile" --region "$region")
    if $remote; then login_options+=(--remote); fi
    aws "${login_options[@]}"
  fi
  aws sts get-caller-identity --profile "$profile" --region "$region" --query '{Account:Account,Identity:Arn}' --output table
  exit
fi
if [[ $command == init ]]; then
  [[ $# -ge 2 ]] || fail 'Usage: deploy/aws.sh init INFRA_DIR --name NAME --admin-cidr IPV4/32 [OPTIONS]'
  directory=$2; shift 2
  [[ ! -e "$directory" ]] || fail 'Destination already exists; edit its aws.tfvars.json instead.'
  name=; cidr=; account=; profile=lean-cloud; region=; machines=1
  machine_size=m7g.large; disk=32; version=; namespace=lean-cloud; zone=
  while [[ $# -gt 0 ]]; do
    [[ $# -ge 2 ]] || fail "Missing value for $1"
    case "$1" in
      --name) name=$2 ;; --admin-cidr) cidr=$2 ;; --account) account=$2 ;; --profile) profile=$2 ;;
      --region) region=$2 ;; --machines) machines=$2 ;; --machine-size) machine_size=$2 ;;
      --os-disk-gib) disk=$2 ;; --kubernetes-version) version=$2 ;; --namespace) namespace=$2 ;;
      --worker-zone) zone=$2 ;; *) fail "Unknown option: $1" ;;
    esac
    shift 2
  done
  identifier "$name"; identifier "$namespace"; number "$machines"; number "$disk"
  [[ ${#name} -le 30 ]] || fail 'Cluster names may contain at most 30 characters'
  valid_profile "$profile"
  [[ -n "$region" ]] || region=$(aws configure get region --profile "$profile" || true)
  [[ -n "$region" ]] || fail "Supply --region or configure a region in the AWS profile"
  valid_region "$region"
  (( machines > 0 && disk >= 32 )) || fail 'Use at least one machine and an OS disk of at least 32 GiB'
  [[ "$machine_size" =~ ^[a-z0-9]+[a-z0-9-]*\.[a-z0-9]+$ ]] || fail 'Invalid EC2 instance type'
  jq -en --arg cidr "$cidr" '$cidr | test("^([0-9]{1,3}\\.){3}[0-9]{1,3}/32$") and
    (split("/")[0] | split(".") | all(tonumber <= 255))' >/dev/null || fail 'Supply your public administrator IPv4 address with /32'
  aws_options=(--profile "$profile" --region "$region")
  actual=$(aws sts get-caller-identity "${aws_options[@]}" --query Account --output text)
  [[ "$actual" =~ ^[0-9]{12}$ ]] || fail 'AWS returned no valid account ID. Sign in explicitly first.'
  [[ -z "$account" || "$account" == "$actual" ]] || fail 'Signed-in AWS account differs from --account'
  account=$actual
  architecture=$(aws ec2 describe-instance-types "${aws_options[@]}" --instance-types "$machine_size" --output json |
    jq -er '.InstanceTypes[0].ProcessorInfo.SupportedArchitectures | if index("arm64") then "arm64" elif index("x86_64") then "amd64" else empty end')
  zones=$(aws ec2 describe-instance-type-offerings "${aws_options[@]}" --location-type availability-zone \
    --filters "Name=instance-type,Values=$machine_size" --output json |
    jq -c --arg region "$region" '[.InstanceTypeOfferings[].Location | select(test("^"+$region+"[a-z]$"))] | unique | sort')
  [[ -n "$zone" ]] || zone=$(jq -er 'first // empty' <<< "$zones")
  jq -en --arg zone "$zone" --argjson zones "$zones" '$zones | index($zone)!=null' >/dev/null || fail 'Machine type is not offered in the selected worker zone'
  versions=$(aws eks describe-cluster-versions "${aws_options[@]}" --output json |
    jq -c '[.clusterVersions[] | select((.versionStatus // .status)=="STANDARD_SUPPORT") | .clusterVersion] | unique | sort_by(split(".")|map(tonumber))')
  [[ -n "$version" ]] || version=$(jq -er 'last // empty' <<< "$versions")
  jq -en --arg version "$version" --argjson versions "$versions" '$versions | index($version)!=null' >/dev/null || fail 'Choose an EKS version in standard support in this region'
  mkdir -p "$directory"; directory=$(absolute_dir "$directory"); private_dir "$directory"
  jq -n --arg name "$name" --arg account "$account" --arg profile "$profile" --arg region "$region" \
    --arg cidr "$cidr" --arg machine "$machine_size" --arg architecture "$architecture" --arg zone "$zone" \
    --arg version "$version" --arg namespace "$namespace" --argjson machines "$machines" --argjson disk "$disk" \
    '{name:$name,account:$account,profile:$profile,region:$region,machines:$machines,machine_size:$machine,
      architecture:$architecture,worker_zone:$zone,os_disk_size_gb:$disk,kubernetes_version:$version,
      administrator_cidrs:[$cidr],namespace:$namespace}' > "$directory/aws.tfvars.json"
  printf 'Created %s/aws.tfvars.json. No cloud resources were created.\n' "$directory"
  jq . "$directory/aws.tfvars.json"
  exit
fi
case "$command" in
  show|plan|create|credentials|storage|destroy-plan|destroy) [[ $# == 2 ]] || fail "Usage: deploy/aws.sh $command INFRA_DIR" ;;
  publish) [[ $# == 4 ]] || fail 'Usage: deploy/aws.sh publish INFRA_DIR LOCAL_IMAGE TAG' ;;
  configure) [[ $# -ge 4 && $# -le 5 ]] || fail 'Usage: deploy/aws.sh configure INFRA_DIR DEPLOYMENT_DIR TAG [WORKERS]' ;;
  *) usage; exit 1 ;;
esac
infra=$(absolute_dir "$2")
case "$command" in
  show) jq . "$infra/aws.tfvars.json"; exit ;;
  plan) bash "$assets/infrastructure.sh" plan aws "$infra" "$infra/aws.tfvars.json"; exit ;;
esac
[[ -f "$infra/provider" && $(cat "$infra/provider") == aws ]] || fail 'Expected an AWS infrastructure state directory'
vars="$infra/terraform.tfvars.json"; cloud="$infra/cloud.json"
profile=$(jq -er .profile "$vars"); region=$(jq -er .region "$vars"); account=$(jq -er .account "$vars")
valid_profile "$profile"; valid_region "$region"
aws_options=(--profile "$profile" --region "$region")
[[ $(aws sts get-caller-identity "${aws_options[@]}" --query Account --output text) == "$account" ]] || fail 'AWS account differs from the planned account'
prepare_storage() {
  need kubectl
  local class existing
  class=$(jq -er .storageClass "$cloud")
  jq -n --arg class "$class" --arg name "$(jq -er .name "$cloud")" \
    '{apiVersion:"storage.k8s.io/v1",kind:"StorageClass",metadata:{name:$class,labels:{"managed-by":"lean-cloud","lean-cloud-cluster":$name}},
      provisioner:"ebs.csi.aws.com",parameters:{type:"gp3",encrypted:"true",tagSpecification_1:("lean-cloud-disk="+$name)},volumeBindingMode:"WaitForFirstConsumer",
      reclaimPolicy:"Delete",allowVolumeExpansion:true}' > "$infra/storageclass.json"
  existing=$(kubectl --kubeconfig "$infra/kubeconfig" get storageclass "$class" --ignore-not-found -o json)
  if [[ -n "$existing" ]]; then
    jq -e --slurpfile wanted "$infra/storageclass.json" '
      .metadata.labels["managed-by"]=="lean-cloud" and .metadata.labels["lean-cloud-cluster"]==$wanted[0].metadata.labels["lean-cloud-cluster"] and
      .provisioner==$wanted[0].provisioner and .parameters==$wanted[0].parameters and
      .volumeBindingMode=="WaitForFirstConsumer" and .reclaimPolicy=="Delete"' <<< "$existing" >/dev/null || fail 'StorageClass exists with different ownership or settings'
  else
    kubectl --kubeconfig "$infra/kubeconfig" create -f "$infra/storageclass.json"
  fi
}
case "$command" in
  create)
    bash "$assets/infrastructure.sh" create "$infra"
    bash "$assets/kubeconfig.sh" "$infra"
    prepare_storage
    printf 'Cluster and storage ready. Use publish, then configure.\n'; exit ;;
  credentials) bash "$assets/kubeconfig.sh" "$infra"; exit ;;
  storage) prepare_storage; exit ;;
  destroy-plan) bash "$assets/infrastructure.sh" destroy-plan "$infra"; exit ;;
  destroy)
    # CSI must finish deleting PVC-backed disks before its cluster disappears.
    # Query by cluster ownership, including disks missing from OpenTofu state.
    name=$(jq -er .name "$vars")
    volumes=$(aws ec2 describe-volumes "${aws_options[@]}" --filters "Name=tag:lean-cloud-disk,Values=$name" --output json)
    jq -e '.Volumes|length==0' <<< "$volumes" >/dev/null || fail 'Cluster EBS volumes remain. Run kubernetes.sh clean while the storage controller is running.'
    bash "$assets/infrastructure.sh" destroy "$infra"
    need tofu
    remaining=$(tofu -chdir="$infra" state list)
    [[ -z "$remaining" ]] || fail 'Infrastructure state still contains resources'
    clusters=$(aws eks list-clusters "${aws_options[@]}" --output json)
    jq -e --arg name "$name" '.clusters|index($name)==null' <<< "$clusters" >/dev/null || fail 'EKS cluster still exists'
    vpcs=$(aws ec2 describe-vpcs "${aws_options[@]}" --filters "Name=tag:lean-cloud-cluster,Values=$name" --output json)
    jq -e '.Vpcs|length==0' <<< "$vpcs" >/dev/null || fail 'Cluster VPC still exists'
    printf 'AWS infrastructure removed. Keep local state until cleanup is verified.\n'; exit ;;
esac
jq -e --arg account "$account" '.provider=="aws" and .account==$account and .storage.provider=="aws"' "$cloud" >/dev/null || fail 'Expected outputs for the planned AWS account'
registry=$(jq -er .registry "$cloud"); repository=$(jq -er .repository "$cloud"); tag=$4
[[ "$repository" == "$registry/"* ]] || fail 'Image repository does not belong to the infrastructure registry'
[[ "$tag" =~ ^[a-zA-Z0-9_][a-zA-Z0-9_.-]{0,127}$ ]] || fail 'Expected an image tag, for example demo-v1'
if [[ $command == publish ]]; then
  need docker
  aws ecr get-login-password "${aws_options[@]}" | docker login --username AWS --password-stdin "$registry"
  docker tag "$3" "$repository:$tag"
  docker push "$repository:$tag"
  printf 'Published %s:%s. Use configure to pin this image and prepare the deployment.\n' "$repository" "$tag"
  exit
fi
need kubectl
directory=$3; workers=${5:-3}; number "$workers"
[[ ! -e "$directory" ]] || fail 'Destination already exists; use a fresh deployment directory.'
[[ -s "$infra/kubeconfig" ]] || fail 'Run deploy/aws.sh credentials for this infrastructure first.'
context=$(kubectl --kubeconfig "$infra/kubeconfig" config current-context)
[[ -n "$context" ]] || fail 'Kubeconfig has no current context'
digest=$(aws ecr describe-images "${aws_options[@]}" --repository-name "${repository#"$registry/"}" --image-ids "imageTag=$tag" --query 'imageDetails[0].imageDigest' --output text)
[[ "$digest" =~ ^sha256:[a-f0-9]{64}$ ]] || fail 'Registry returned no valid image digest. Push the image first.'
mkdir -p "$directory"; directory=$(absolute_dir "$directory"); private_dir "$directory"
jq --slurpfile infra "$cloud" --arg context "$context" --arg namespace "$(jq -er .namespace "$vars")" \
  --arg kubeconfig "$infra/kubeconfig" --arg digest "$digest" --argjson workers "$workers" '
  $infra[0] as $i | .name=$i.name | .context=$context | .kubeconfig=$kubeconfig | .namespace=$namespace |
  .image=($i.repository+"@"+$digest) | .workers=$workers | .storageClass=$i.storageClass
  ' "$assets/kubernetes/deployment.example.json" > "$directory/deployment.json"
jq '.storage | {provider:"s3",endpoint:("https://s3."+.region+".amazonaws.com"),
  bucket:.bucket,region:.region,authentication:{kind:.authentication},provisioned:true}' "$cloud" > "$directory/storage.json"
bash "$assets/kubernetes.sh" render "$directory"
printf 'Created %s with %s workers. No cloud resources were changed.\n' "$directory" "$workers"
printf 'Review the files, then run: deploy/kubernetes.sh up "%s"\n' "$directory"
