#!/usr/bin/env bash
# Exercise the AWS helper with fake provider tools; no credentials or cloud costs.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$root"
work=$(mktemp -d); work=$(cd "$work" && pwd -P)
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin"
export HELPER_AWS_WORK="$work"
cat > "$work/bin/aws" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf 'aws %s\n' "$*" >> "$HELPER_AWS_WORK/calls"
case "$*" in
  --version) echo "aws-cli/${AWS_TEST_VERSION:-2.33.0}" ;;
  'configure get region '*) [[ ${AWS_TEST_NO_REGION:-0} == 0 ]] && echo eu-north-1 ;;
  'login '*|'sso login '*) ;;
  'sts get-caller-identity '*) echo "${AWS_TEST_ACCOUNT:-111111111111}" ;;
  'eks describe-cluster-versions '*) echo '{"clusterVersions":[{"clusterVersion":"1.9","status":"EXTENDED_SUPPORT"},{"clusterVersion":"1.35","versionStatus":"STANDARD_SUPPORT"},{"clusterVersion":"1.36","status":"STANDARD_SUPPORT"}]}' ;;
  'ec2 describe-instance-types '*)
    if [[ "$*" == *m7i.large* ]]; then arch=x86_64; else arch=arm64; fi
    printf '{"InstanceTypes":[{"ProcessorInfo":{"SupportedArchitectures":["%s"]}}]}\n' "$arch" ;;
  'ec2 describe-instance-type-offerings '*) echo '{"InstanceTypeOfferings":[{"Location":"eu-north-1b"},{"Location":"eu-north-1a"}]}' ;;
  'eks update-kubeconfig '*)
    while [[ $1 != --kubeconfig ]]; do shift; done
    echo credentials > "$2" ;;
  'ecr get-login-password '*) echo test-password ;;
  'ecr describe-images '*)
    if [[ ${AWS_TEST_BAD_DIGEST:-0} == 1 ]]; then echo invalid; else printf 'sha256:%064d\n' 1; fi ;;
  'ec2 describe-volumes '*)
    if [[ ${AWS_TEST_DISKS:-0} == 1 ]]; then echo '{"Volumes":[{"VolumeId":"leftover"}]}'; else echo '{"Volumes":[]}'; fi ;;
  'eks list-clusters '*) echo '{"clusters":[]}' ;;
  'ec2 describe-vpcs '*)
    if [[ ${AWS_TEST_VPC:-0} == 1 ]]; then echo '{"Vpcs":[{}]}'; else echo '{"Vpcs":[]}'; fi ;;
  *) echo "Unexpected AWS call: $*" >&2; exit 1 ;;
esac
MOCK
cat > "$work/bin/tofu" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf 'tofu %s\n' "$*" >> "$HELPER_AWS_WORK/calls"
directory=${1#-chdir=}; shift
case "$*" in
  init) [[ ${AWS_TEST_INIT_FAIL:-0} == 0 ]] ;;
  'plan -out=provision.tfplan.pending')
    touch "$directory/${2#-out=}"
    [[ ${AWS_TEST_PLAN_FAIL:-0} == 0 ]] ;;
  'plan -destroy -out=destroy.tfplan.pending')
    touch "$directory/${3#-out=}"
    [[ ${AWS_TEST_PLAN_FAIL:-0} == 0 ]] ;;
  'apply provision.tfplan') [[ -f "$directory/provision.tfplan" ]] ;;
  'apply destroy.tfplan') [[ -f "$directory/destroy.tfplan" ]] ;;
  'state list') [[ ${AWS_TEST_STATE_FAIL:-0} == 0 ]] ;;
  'output -json cloud')
    if [[ ${AWS_TEST_OUTPUT_FAIL:-0} == 1 ]]; then printf '{partial'; exit 1; fi
    if [[ ${AWS_TEST_OUTPUT_INVALID:-0} == 1 ]]; then printf 'null'; else cat "$HELPER_AWS_WORK/cloud.json"; fi ;;
  *) echo "Unexpected OpenTofu call: $*" >&2; exit 1 ;;
esac
MOCK
cat > "$work/bin/kubectl" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf 'kubectl %s\n' "$*" >> "$HELPER_AWS_WORK/calls"
case "$*" in
  *' config current-context') echo aws-demo ;;
  *' get storageclass '*)
    if [[ ${AWS_TEST_FOREIGN_CLASS:-0} == 1 ]]; then echo '{"metadata":{"labels":{}}}'
    elif [[ -f "$HELPER_AWS_WORK/storageclass.json" ]]; then cat "$HELPER_AWS_WORK/storageclass.json"; fi ;;
  *' create -f '*) cp "${!#}" "$HELPER_AWS_WORK/storageclass.json" ;;
  *' get nodes -o wide'|*' get pods -l lean-cloud/deployment=aws-demo -o wide') ;;
  *' port-forward --address 127.0.0.1 service/cloud-api 8081:8080') ;;
  *) echo "Unexpected Kubernetes call: $*" >&2; exit 1 ;;
esac
MOCK
cat > "$work/bin/docker" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf 'docker %s\n' "$*" >> "$HELPER_AWS_WORK/calls"
case "$*" in
  info|'buildx version'|'tag '*) ;;
  'login --username AWS --password-stdin '*) read -r password; [[ $password == test-password ]] ;;
  'push '*) [[ ${AWS_TEST_PUSH_FAIL:-0} == 0 ]] ;;
  *) echo "Unexpected Docker call: $*" >&2; exit 1 ;;
esac
MOCK
chmod +x "$work/bin/"*
export PATH="$work/bin:$PATH"
cat > "$work/cloud.json" <<'JSON'
{"provider":"aws","name":"aws-demo","region":"eu-north-1","account":"111111111111",
 "registry":"111111111111.dkr.ecr.eu-north-1.amazonaws.com","repository":"111111111111.dkr.ecr.eu-north-1.amazonaws.com/lean-cloud-aws-demo",
 "storageClass":"lean-cloud-aws-demo-gp3","storage":{"provider":"aws","region":"eu-north-1","bucket":"example-bucket","authentication":"podIdentity"}}
JSON
infra="$work/aws infra"; deployment="$work/aws deployment"
bash deploy/aws.sh doctor
bash deploy/aws.sh login lean-cloud --remote
bash deploy/aws.sh login company --sso --region eu-north-1
: > "$work/calls"
bash deploy/aws.sh init "$infra" --name aws-demo --admin-cidr 192.0.2.1/32
jq -e '.region=="eu-north-1" and .machines==1 and .architecture=="arm64" and .worker_zone=="eu-north-1a" and .kubernetes_version=="1.36" and .os_disk_size_gb==32' "$infra/aws.tfvars.json" >/dev/null
if grep -q 'apply\|aws login' "$work/calls"; then echo 'init provisioned or signed in'; exit 1; fi
bash deploy/aws.sh show "$infra" > "$work/shown.json"
cmp "$infra/aws.tfvars.json" "$work/shown.json"
if bash deploy/aws.sh init "$infra" --name other --admin-cidr 192.0.2.1/32 2>/dev/null; then echo 'Overwrote config'; exit 1; fi
for cidr in 999.1.2.3/32 192.0.2.1/0; do
  if bash deploy/aws.sh init "$work/bad" --name bad --admin-cidr "$cidr" 2>/dev/null; then exit 1; fi
done
if AWS_TEST_NO_REGION=1 bash deploy/aws.sh init "$work/bad" --name bad --admin-cidr 192.0.2.1/32 2>/dev/null; then echo 'Guessed a region'; exit 1; fi
if bash deploy/aws.sh init "$work/bad" --name bad --admin-cidr 192.0.2.1/32 --account 222222222222 2>/dev/null; then echo 'Accepted different account'; exit 1; fi
if bash deploy/aws.sh init "$work/bad" --name bad --admin-cidr 192.0.2.1/32 --worker-zone eu-north-1z 2>/dev/null; then echo 'Accepted unsupported zone'; exit 1; fi
if bash deploy/aws.sh init "$work/bad" --name bad --admin-cidr 192.0.2.1/32 --kubernetes-version 1.9 2>/dev/null; then echo 'Accepted extended support'; exit 1; fi
[[ ! -e "$work/bad" ]]
bash deploy/aws.sh init "$work/custom" --name custom --admin-cidr 192.0.2.1/32 --machine-size m7i.large --machines 2 --os-disk-gib 128 --worker-zone eu-north-1b --namespace custom --kubernetes-version 1.35
jq -e '.architecture=="amd64" and .os_disk_size_gb==128 and .worker_zone=="eu-north-1b"' "$work/custom/aws.tfvars.json" >/dev/null
bash deploy/aws.sh plan "$infra"
cmp deploy/infrastructure/aws/.terraform.lock.hcl "$infra/.terraform.lock.hcl"
# Failed initialization/planning must not leave an older plan applicable. The
# mock also leaves a partial output, as a killed provider could do.
for fault in AWS_TEST_INIT_FAIL AWS_TEST_PLAN_FAIL; do
  if env "$fault=1" bash deploy/aws.sh plan "$infra" 2>/dev/null; then echo 'Ignored planning failure'; exit 1; fi
  [[ ! -e "$infra/provision.tfplan" && ! -e "$infra/destroy.tfplan" ]] || { echo 'Failed re-plan kept an applicable plan'; exit 1; }
  if bash deploy/aws.sh create "$infra" 2>/dev/null; then echo 'Applied after failed planning'; exit 1; fi
  bash deploy/aws.sh plan "$infra"
done
bash deploy/aws.sh destroy-plan "$infra"
if AWS_TEST_PLAN_FAIL=1 bash deploy/aws.sh destroy-plan "$infra" 2>/dev/null; then echo 'Ignored deletion planning failure'; exit 1; fi
[[ ! -e "$infra/destroy.tfplan" && ! -e "$infra/provision.tfplan" ]] || { echo 'Failed deletion re-plan kept an applicable plan'; exit 1; }
bash deploy/aws.sh destroy-plan "$infra"
bash deploy/aws.sh plan "$infra"
[[ ! -e "$infra/destroy.tfplan" ]] || { echo 'New plan kept an old deletion plan'; exit 1; }
printf azure > "$infra/provider"
if bash deploy/aws.sh create "$infra" 2>/dev/null; then echo 'Applied another provider plan'; exit 1; fi
printf aws > "$infra/provider"
if AWS_TEST_ACCOUNT=222222222222 bash deploy/aws.sh create "$infra" 2>/dev/null; then echo 'Applied to wrong account'; exit 1; fi
jq '.machines=3' "$infra/aws.tfvars.json" > "$work/edited.json"; mv "$work/edited.json" "$infra/aws.tfvars.json"
bash deploy/aws.sh create "$infra"
jq -e '.machines==1' "$infra/terraform.tfvars.json" >/dev/null
jq -e '.provisioner=="ebs.csi.aws.com" and .parameters.encrypted=="true" and .parameters.tagSpecification_1=="lean-cloud-disk=aws-demo" and .volumeBindingMode=="WaitForFirstConsumer" and .reclaimPolicy=="Delete"' "$work/storageclass.json" >/dev/null
# Re-planning must not redirect cleanup/credentials to a different cluster or
# move the development node pool away from its durable disks.
cp "$infra/terraform.tfvars.json" "$work/saved-vars.json"
cp "$infra/aws.tfvars.json" "$work/editable-vars.json"
for change in '.name="another-cluster"' '.account="222222222222"' '.region="eu-west-1"' '.namespace="another-namespace"' '.worker_zone="eu-north-1b"'; do
  jq "$change" "$work/editable-vars.json" > "$infra/aws.tfvars.json"
  : > "$work/calls"
  if bash deploy/aws.sh plan "$infra" > "$work/result" 2>&1; then echo 'Changed the identity of existing infrastructure'; exit 1; fi
  grep -Fq 'Use a fresh infrastructure directory' "$work/result"
  cmp "$work/saved-vars.json" "$infra/terraform.tfvars.json"
  if grep -q '^tofu ' "$work/calls"; then echo 'Contacted provider after identity change'; exit 1; fi
done
cp "$work/editable-vars.json" "$infra/aws.tfvars.json"
# Ordinary capacity changes still plan successfully, and cleanup keeps the
# original cluster's identity even before that new capacity plan is applied.
bash deploy/aws.sh plan "$infra"
jq -e '.machines==3 and .name=="aws-demo"' "$infra/terraform.tfvars.json" >/dev/null
bash deploy/aws.sh credentials "$infra"
# A failed output refresh must preserve the last complete metadata. Credentials
# must also recover missing metadata after apply, without applying resources again.
if AWS_TEST_OUTPUT_FAIL=1 bash deploy/infrastructure.sh create "$infra" 2>/dev/null; then echo 'Ignored output failure'; exit 1; fi
cmp "$work/cloud.json" "$infra/cloud.json"
rm "$infra/cloud.json"
: > "$work/calls"
for fault in AWS_TEST_OUTPUT_FAIL AWS_TEST_OUTPUT_INVALID; do
  if env "$fault=1" bash deploy/aws.sh credentials "$infra" 2>/dev/null; then echo 'Accepted incomplete cluster metadata'; exit 1; fi
  [[ ! -e "$infra/cloud.json" ]] || { echo 'Published incomplete cluster metadata'; exit 1; }
done
bash deploy/aws.sh credentials "$infra"
cmp "$work/cloud.json" "$infra/cloud.json"
if grep -q 'apply' "$work/calls"; then echo 'Reapplied resources to recover credentials'; exit 1; fi
bash deploy/aws.sh storage "$infra"
if AWS_TEST_FOREIGN_CLASS=1 bash deploy/aws.sh storage "$infra" 2>/dev/null; then echo 'Adopted foreign storage class'; exit 1; fi
if AWS_TEST_PUSH_FAIL=1 bash deploy/aws.sh publish "$infra" app:dev demo; then echo 'Ignored failed push'; exit 1; fi
bash deploy/aws.sh publish "$infra" app:dev demo
if AWS_TEST_BAD_DIGEST=1 bash deploy/aws.sh configure "$infra" "$deployment" demo 3 2>/dev/null; then echo 'Accepted invalid digest'; exit 1; fi
[[ ! -e "$deployment" ]]
bash deploy/aws.sh configure "$infra" "$deployment" demo 3
jq -e --arg kubeconfig "$infra/kubeconfig" '.workers==3 and .kubeconfig==$kubeconfig and .storageClass=="lean-cloud-aws-demo-gp3" and .serviceAccountAnnotations=={} and (.image|test("@sha256:"))' "$deployment/deployment.json" >/dev/null
jq -e '.endpoint=="https://s3.eu-north-1.amazonaws.com" and .authentication.kind=="podIdentity" and .provisioned==true' "$deployment/storage.json" >/dev/null
jq -e '[.items[]|select(.kind=="StatefulSet")]|length==4' "$deployment/resources.json" >/dev/null
if bash deploy/aws.sh configure "$infra" "$deployment" demo 3 2>/dev/null; then echo 'Overwrote deployment'; exit 1; fi
export KUBECONFIG="$work/unrelated"
bash deploy/kubernetes.sh status "$deployment"
bash deploy/kubernetes.sh connect "$deployment" 8081
if grep -q '^aws login\|test-password' "$work/calls"; then echo 'Implicit login or leaked password'; exit 1; fi
bash deploy/aws.sh destroy-plan "$infra"
: > "$work/calls"
if AWS_TEST_DISKS=1 bash deploy/aws.sh destroy "$infra" 2>/dev/null; then echo 'Destroyed before disk cleanup'; exit 1; fi
if grep -q 'apply destroy' "$work/calls"; then echo 'Deleted storage controller too soon'; exit 1; fi
if AWS_TEST_VPC=1 bash deploy/aws.sh destroy "$infra" 2>/dev/null; then echo 'Ignored remaining VPC'; exit 1; fi
if AWS_TEST_STATE_FAIL=1 bash deploy/aws.sh destroy "$infra" 2>/dev/null; then echo 'Mistook failed state check for successful cleanup'; exit 1; fi
bash deploy/aws.sh destroy "$infra"
for version in 1.32.0 2.9.0 2.31.99; do
  if AWS_TEST_VERSION=$version bash deploy/aws.sh doctor >/dev/null 2>&1; then echo 'Doctor accepted an unsupported AWS CLI'; exit 1; fi
  if AWS_TEST_VERSION=$version bash deploy/aws.sh login lean-cloud --remote >/dev/null 2>&1; then echo 'Started browser login with unsupported AWS CLI'; exit 1; fi
done
AWS_TEST_VERSION=2.32.0 bash deploy/aws.sh doctor
printf 'AWS command workflow contracts passed.\n'
