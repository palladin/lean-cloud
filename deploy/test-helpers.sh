#!/usr/bin/env bash
# Offline contracts for generated files and destructive-operation guards.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$root"
need() { command -v "$1" >/dev/null; }
need jq
need rg
for script in deploy/*.sh; do bash -n "$script"; done
if command -v shellcheck >/dev/null; then shellcheck -S warning deploy/*.sh; fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin"
export HELPER_TEST_LOG="$work/calls"
cat > "$work/bin/docker" <<'MOCK'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$HELPER_TEST_LOG"
case "$*" in
  'image inspect '* ) printf 'sha256:%064d\n' 1 ;;
  'info --format {{.Name}}') printf 'test-machine\n' ;;
  info|'compose version'|'buildx version') ;;
  *'volume inspect'*) exit 1 ;;
  *'compose '*down*) ;;
  *'compose '*port*) printf '127.0.0.1:8080\n' ;;
  *'compose '*ps) ;;
  'buildx build '* | 'build '*) ;;
  'volume create '*|*'compose '*stop|*'compose '*up*) [[ ${HELPER_TEST_START:-0} == 1 ]] ;;
  *'compose '*pool-configure*) [[ ${HELPER_TEST_START:-0} == 1 ]] && cat > "$HELPER_TEST_MEMBERSHIP" ;;
  *'compose '*pool-workers*) [[ ${HELPER_TEST_START:-0} == 1 ]] && printf '{"generation":0}' ;;
  *) echo 'Unexpected Docker action during offline test' >&2; exit 1 ;;
esac
MOCK
chmod +x "$work/bin/docker"
cat > "$work/bin/curl" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
url=${!#}
[[ "$url" == https://api.github.com/repos/leanprover/lean4/releases/tags/v* ]] || exit 1
if [[ ${HELPER_BAD_RELEASE:-0} == 1 ]]; then printf '{"assets":[]}\n'; exit; fi
version=${url##*/v}
printf '{"assets":[{"name":"lean-%s-linux.tar.zst","digest":"sha256:%064d"},{"name":"lean-%s-linux_aarch64.tar.zst","digest":"sha256:%064d"}]}\n' "$version" 1 "$version" 2
MOCK
chmod +x "$work/bin/curl"
export PATH="$work/bin:$PATH"
bash deploy/local.sh doctor
assert_mode() {
  local actual
  actual=$(stat -c '%a' "$2" 2>/dev/null || stat -f '%Lp' "$2")
  [[ "$actual" == "$1" ]] || { echo "Expected mode $1 for $2, got $actual"; exit 1; }
}
for count in 0 1 6; do
  dir="$work/local-$count"
  bash deploy/local.sh configure "$dir" app:test "test-$count" "$count" 8080
  bash deploy/local.sh show "$dir" > "$work/shown.json"
  cmp "$dir/deployment.json" "$work/shown.json"
  bash deploy/local.sh status "$dir"
  bash deploy/local.sh connect "$dir" > "$work/connection"
  grep -Fq "connect test-$count http://127.0.0.1:8080" "$work/connection"
  # Native Linux bind mounts preserve host modes; containers use different UIDs.
  assert_mode 700 "$dir"
  for file in config.json s3.json filer.toml; do assert_mode 644 "$dir/$file"; done
  for file in client.token internal.token blob-access.token blob-secret.token; do
    assert_mode 600 "$dir/$file"
  done
  jq -e --argjson count "$count" '.services|length==$count+2' "$dir/compose.json" >/dev/null
  jq -e '[.services|to_entries[]|select(.key!="blobs")|.value.environment.CLOUD_NODE_NAME]|all(.=="test-machine")' "$dir/compose.json" >/dev/null
  jq -e --argjson count "$count" '.mailboxes.workers|length==$count' "$dir/config.json" >/dev/null
  jq -e '.formatVersion==1 and (.worker|type)=="object" and .blobs.provider=="s3"' "$dir/config.json" >/dev/null
  jq -e '.mailboxes.workers|all(.cpus==1 and .memoryMiB==null)' "$dir/config.json" >/dev/null
  jq -e '.client.token!=.mailboxes.scheduler.token and (.client.token|length)==64' "$dir/config.json" >/dev/null
  jq -e --slurpfile s3 "$dir/s3.json" '
    (.blobs.authentication.accessKey|length)==32 and (.blobs.authentication.secretKey|length)==64 and
    .blobs.authentication.secretKey!=.client.token and .blobs.authentication.secretKey!=.mailboxes.scheduler.token and
    .blobs.authentication.accessKey==$s3[0].identities[0].credentials[0].accessKey and
    .blobs.authentication.secretKey==$s3[0].identities[0].credentials[0].secretKey
    ' "$dir/config.json" >/dev/null
  grep -Fxq '*' "$dir/.gitignore"
  jq -e '.services.scheduler.ports==["127.0.0.1:8080:8080"] and .services.scheduler.image=="sha256:0000000000000000000000000000000000000000000000000000000000000001"' "$dir/compose.json" >/dev/null
  jq -e '[.services|to_entries[]|select(.key!="blobs")|.value.volumes[0]] | length==(unique|length)' "$dir/compose.json" >/dev/null
  if bash deploy/local.sh configure "$dir" other:image test 9 8080 2>/dev/null; then echo 'Overwrote existing deployment'; exit 1; fi
  if bash deploy/local.sh clean "$dir" 2>/dev/null; then echo 'Clean did not require --yes'; exit 1; fi
done
[[ $(jq -r .blobs.authentication.secretKey "$work/local-0/config.json") != "$(jq -r .blobs.authentication.secretKey "$work/local-1/config.json")" ]]
# A recorded missing durable volume must stop recovery before any container starts.
printf '["test-0_scheduler-data"]' > "$work/local-0/volumes.json"
if bash deploy/local.sh up "$work/local-0" 2>/dev/null; then echo 'Started with lost durable state'; exit 1; fi
if grep -q 'compose.*up' "$HELPER_TEST_LOG"; then echo 'Started nodes before volume check'; exit 1; fi
[[ ! -d "$work/local-0/.operation" ]]
# Cleanup can be retried after some volumes have already been deleted.
bash deploy/local.sh clean "$work/local-0" --yes
bash deploy/local.sh clean "$work/local-0" --yes
if bash deploy/local.sh up "$work/local-0" > "$work/result" 2>&1; then echo 'Started cleaned deployment'; exit 1; fi
grep -Fq 'Cleanup has started' "$work/result"
if bash deploy/local.sh scale "$work/local-0" 3 > "$work/result" 2>&1; then echo 'Scaled cleaned deployment'; exit 1; fi

# Invalid resource edits must fail before stopping nodes, but must not prevent
# inspecting or removing the already-rendered deployment. False is not "unset".
for resources in '{"cpuMillis":false}' '{"memoryMiB":false}' '{"cpuMillis":0}' '{"memoryMiB":-1}' '{"cpuMillis":1.5}' '{"memoryMiB":"2048"}'; do
  jq --argjson resources "$resources" 'del(.cpuMillis,.memoryMiB) + $resources' "$work/local-6/deployment.json" > "$work/next.json"
  mv "$work/next.json" "$work/local-6/deployment.json"
  : > "$HELPER_TEST_LOG"
  for command in up 'scale 6'; do
    read -r operation count <<< "$command"
    if bash deploy/local.sh "$operation" "$work/local-6" ${count:+"$count"} > "$work/result" 2>&1; then
      echo 'Invalid resource budget accepted'; exit 1
    fi
    grep -Fq 'Invalid worker CPU or memory budget' "$work/result"
  done
  [[ ! -s "$HELPER_TEST_LOG" ]] || { echo 'Invalid resources reached Docker'; exit 1; }
done
bash deploy/local.sh show "$work/local-6" > "$work/shown.json"
HELPER_TEST_START=1 bash deploy/local.sh down "$work/local-6"
bash deploy/local.sh clean "$work/local-6" --yes

# Resource edits take effect through the same stop/render/start barrier as scaling.
jq '.cpuMillis=2500 | .memoryMiB=2048' "$work/local-1/deployment.json" > "$work/next.json"
mv "$work/next.json" "$work/local-1/deployment.json"
HELPER_TEST_START=1 HELPER_TEST_MEMBERSHIP="$work/local-membership.json" bash deploy/local.sh scale "$work/local-1" 1
jq -e '.services.worker1|.cpus==2.5 and .mem_limit=="2048m"' "$work/local-1/compose.json" >/dev/null
jq -e 'length==1 and all(.cpus==2 and .memoryMiB==2048)' "$work/local-membership.json" >/dev/null

mkdir "$work/kube"
jq '.image="registry/app@sha256:0000000000000000000000000000000000000000000000000000000000000001"' \
  deploy/kubernetes/deployment.example.json > "$work/kube/deployment.json"
bash deploy/kubernetes.sh render "$work/kube"
jq -e '[.items[]|select(.kind=="StatefulSet")]|length==4 and all(.spec.replicas==0 and .spec.updateStrategy.type=="OnDelete" and .spec.persistentVolumeClaimRetentionPolicy.whenDeleted=="Retain")' "$work/kube/resources.json" >/dev/null
jq -e '[.items[]|select(.kind=="Service")]|all(.spec.type=="ClusterIP")' "$work/kube/resources.json" >/dev/null
jq -e '[.items[]|select(.kind=="PersistentVolumeClaim")]|length==4' "$work/kube/resources.json" >/dev/null
jq -e '[.items[]|select(.kind=="StatefulSet")|.spec.template.spec.containers[0].env[]|select(.name=="CLOUD_NODE_NAME")]|length==4 and all(.valueFrom.fieldRef.fieldPath=="spec.nodeName")' "$work/kube/resources.json" >/dev/null
if grep -q 'token\|secretKey' "$work/kube/resources.json"; then echo 'Credentials in preview'; exit 1; fi
jq '.startupSeconds=900' "$work/kube/deployment.json" > "$work/kube/next.json"
mv "$work/kube/next.json" "$work/kube/deployment.json"
bash deploy/kubernetes.sh render "$work/kube"
jq -e '[.items[]|select(.kind=="StatefulSet")|.spec.template.spec.containers[0].startupProbe.failureThreshold]|all(.==180)' "$work/kube/resources.json" >/dev/null
jq '.schedulerResources={cpuMillis:250,memoryMiB:512}' "$work/kube/deployment.json" > "$work/kube/next.json"
mv "$work/kube/next.json" "$work/kube/deployment.json"
bash deploy/kubernetes.sh render "$work/kube"
jq -e '.items[]|select(.kind=="StatefulSet" and .metadata.name=="scheduler")|.spec.template.spec.containers[0].resources|.requests.cpu=="250m" and .limits.memory=="512Mi"' "$work/kube/resources.json" >/dev/null
jq -e --arg memory "$(jq -r '.memoryMiB|tostring' "$work/kube/deployment.json")Mi" '[.items[]|select(.kind=="StatefulSet" and .metadata.name!="scheduler")|.spec.template.spec.containers[0].resources.limits.memory]|all(.==$memory)' "$work/kube/resources.json" >/dev/null
cp "$work/kube/deployment.json" "$work/kube/valid.json"
for request in 'null' 'false' '0' '-1' '1.5' '"100"' '999999'; do
  jq --argjson request "$request" '.cpuRequestMillis=$request' "$work/kube/valid.json" > "$work/kube/deployment.json"
  if bash deploy/kubernetes.sh render "$work/kube" 2>/dev/null; then echo "Accepted invalid CPU request: $request"; exit 1; fi
done
cp "$work/kube/valid.json" "$work/kube/deployment.json"
jq '.image="mutable:tag"' "$work/kube/deployment.json" > "$work/kube/next.json"
mv "$work/kube/next.json" "$work/kube/deployment.json"
if bash deploy/kubernetes.sh render "$work/kube" 2>/dev/null; then echo 'Accepted mutable registry image'; exit 1; fi
bash deploy/new-app.sh "$work/example" "$root"
[[ -f "$work/example/Main.lean" && -f "$work/example/lakefile.lean" ]]
cmp .gitignore "$work/example/.gitignore"
cmp .dockerignore "$work/example/.dockerignore"
# Custom state paths and provider files must stay out of an application's Git index.
git -C "$work/example" init -q
for path in custom-state/config.json custom-state/config.next custom-state/storage.json custom-state/s3.json \
    custom-state/client.token custom-state/kubeconfig custom-state/kubeconfig.yaml custom-state/cloud.json \
    custom-state/deployment.json custom-state/resources.json custom-state/compose.json \
    custom-state/terraform.tfstate custom-state/provision.tfplan custom-state/private.tfvars \
    custom-state/private.tfvars.json custom-state/.terraform/credentials.json \
    .env .env.private .aws/credentials .azure/accessTokens.json .kube/config lean-cloud.local.json; do
  git -C "$work/example" check-ignore -q "$path" || { echo "Unprotected private file: $path"; exit 1; }
done
for path in deploy/config.json deploy/s3.json deploy/kubeconfig.sh; do
  if git -C "$work/example" check-ignore -q "$path"; then echo "Ignored public source: $path"; exit 1; fi
done
if bash deploy/new-app.sh "$work/example" 2>/dev/null; then echo 'Replaced an existing application'; exit 1; fi
# LeanBuild accepts newer source releases independently of the worker SDK pin.
for version in 4.35.0 4.35.1 4.36.0 4.100.0 5.0.0; do
  : > "$HELPER_TEST_LOG"
  bash Applications/LeanBuild/build.sh lean-build:test "$version"
  [[ $(wc -l < "$HELPER_TEST_LOG") -eq 2 ]]
  grep -Fq -- "--build-arg SOURCE_LEAN_VERSION=$version -t lean-build:test" "$HELPER_TEST_LOG"
done
: > "$HELPER_TEST_LOG"
if HELPER_BAD_RELEASE=1 bash Applications/LeanBuild/build.sh lean-build:test 4.35.0; then
  echo 'Built an image without official release checksums'; exit 1
fi
[[ ! -s "$HELPER_TEST_LOG" ]]
: > "$HELPER_TEST_LOG"
bash Applications/LeanBuild/build.sh
grep -Fq -- "--build-arg SOURCE_LEAN_VERSION=$(sed 's|leanprover/lean4:v||' Applications/LeanBuild/source-toolchain)" "$HELPER_TEST_LOG"
for version in 3.99.0 4.9.0 4.34.99 4.35 04.35.0 4.035.0 4.35.00 4.35.0-rc1 nightly; do
  : > "$HELPER_TEST_LOG"
  if bash Applications/LeanBuild/build.sh lean-build:test "$version" 2>/dev/null; then
    echo "Unsupported source version accepted: $version"; exit 1
  fi
  [[ ! -s "$HELPER_TEST_LOG" ]] || { echo 'Invalid version reached Docker'; exit 1; }
done
# The production client has no provider/container/command execution path.
if rg '"(docker|kubectl|tofu|az|aws)"|startProcess|pollProcess|HostOp.*process' LeanCloudCli; then
  echo 'Infrastructure leaked into CLI'; exit 1
fi
printf 'Deployment helper contracts passed.\n'
bash deploy/test-kubernetes.sh
bash deploy/test-azure.sh
bash deploy/test-aws.sh
