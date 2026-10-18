#!/usr/bin/env bash
# Offline lifecycle contracts: a failed stop or replaced PVC must prevent restart.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin" "$work/deployment"
export HELPER_KUBE_WORK="$work"
export HELPER_KUBE_MODE=replaced
jq '.image="registry/app@sha256:0000000000000000000000000000000000000000000000000000000000000001"' \
  deploy/kubernetes/deployment.example.json > "$work/deployment/deployment.json"
cp deploy/kubernetes/storage.azure.example.json "$work/deployment/storage.json"
identity=$(jq -Sc 'del(.workers,.cpuMillis,.memoryMiB)' "$work/deployment/deployment.json")
storage_hash=$(jq -Sc . "$work/deployment/storage.json" | shasum -a 256 | cut -d ' ' -f 1)
name=$(jq -r .name "$work/deployment/deployment.json")
jq -n --arg identity "$identity" --arg storage "$storage_hash" \
  '{data:{identity:$identity,storage:$storage,claims:"[{\"name\":\"state-scheduler-0\",\"uid\":\"original\"}]"}}' > "$work/record.json"
jq -n --arg name "$name" '{metadata:{labels:{"lean-cloud/deployment":$name,"app.kubernetes.io/managed-by":"lean-cloud"}}}' > "$work/namespace.json"
cat > "$work/bin/kubectl" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$*" >> "$HELPER_KUBE_WORK/calls"
case "$*" in
  *' get namespace '*)
    if [[ ! -f "$HELPER_KUBE_WORK/namespace-deleted" ]]; then cat "$HELPER_KUBE_WORK/namespace.json"; fi ;;
  *' get configmap cloud-deployment '*) cat "$HELPER_KUBE_WORK/record.json" ;;
  *' create configmap cloud-operation '*|*' delete configmap cloud-operation '*) ;;
  *' get pvc state-scheduler-0 '*)
    if [[ "$HELPER_KUBE_MODE" == replaced ]]; then printf '{"metadata":{"uid":"replacement"}}'
    else printf '{"metadata":{"uid":"original","labels":{"lean-cloud/deployment":"lean-cloud","lean-cloud/role":"scheduler"}}}'; fi ;;
  *' get pvc state-worker'*) ;;
  *' get pvc -l '*) printf '{"items":[{"metadata":{"name":"state-scheduler-0","uid":"original"}}]}' ;;
  *' get statefulsets '*) printf '{"items":[{"metadata":{"name":"scheduler"}},{"metadata":{"name":"worker1"}}]}' ;;
  *' scale statefulset/'*) ;;
  *' create configmap cloud-deployment '*|*' create secret generic cloud-config '*) printf '{}' ;;
  *' apply -f -') cat >/dev/null ;;
  *' apply -f '*) ;;
  *' exec -i scheduler-0 -- cloud-app pool-configure '*) cat > "$HELPER_KUBE_WORK/membership.json" ;;
  *' exec scheduler-0 -- cloud-app pool-workers '*) printf '{"generation":1}' ;;
  *' exec scheduler-0 -- cloud-app pool-stopped '*) ;;
  *' wait --for=create pod/'*|*' wait --for=condition=Ready pod/'*) ;;
  *' port-forward --address 127.0.0.1 service/cloud-api '*) ;;
  *' wait --for=delete pod '*) [[ "$HELPER_KUBE_MODE" != stop-failed ]] ;;
  *' get pv -o json')
    policy=Delete
    [[ "$HELPER_KUBE_MODE" != retain ]] || policy=Retain
    printf '{"items":[{"metadata":{"name":"test-disk"},"spec":{"claimRef":{"namespace":"lean-cloud"},"persistentVolumeReclaimPolicy":"%s"}},{"metadata":{"name":"unrelated-disk"},"spec":{"claimRef":{"namespace":"other"},"persistentVolumeReclaimPolicy":"Delete"}}]}' "$policy" ;;
  *' delete namespace '*) touch "$HELPER_KUBE_WORK/namespace-deleted" ;;
  *' wait --for=delete namespace/'*) touch "$HELPER_KUBE_WORK/namespace-deleted" ;;
  *' get pv test-disk '*)
    [[ "$HELPER_KUBE_MODE" != pv-error ]] || exit 1
    if [[ ! -f "$HELPER_KUBE_WORK/pv-deleted" ]]; then printf 'persistentvolume/test-disk\n'; fi ;;
  *' wait --for=delete pv/test-disk '*)
    [[ "$HELPER_KUBE_MODE" != pv-timeout ]] || exit 1
    touch "$HELPER_KUBE_WORK/pv-deleted" ;;
  *) echo "Unexpected Kubernetes operation: $*" >&2; exit 1 ;;
esac
MOCK
chmod +x "$work/bin/kubectl"
export PATH="$work/bin:$PATH"
if bash deploy/kubernetes.sh up "$work/deployment" > "$work/result" 2>&1; then echo 'Accepted replacement PVC'; exit 1; fi
grep -q 'Durable claim replaced' "$work/result"
if grep -q 'scale\| apply ' "$work/calls"; then echo 'Changed deployment before validating durable claims'; exit 1; fi
export HELPER_KUBE_MODE=stop-failed
: > "$work/calls"
if bash deploy/kubernetes.sh up "$work/deployment" > "$work/result" 2>&1; then echo 'Ignored stop failure'; exit 1; fi
grep -q 'scale statefulset/scheduler --replicas=0' "$work/calls"
grep -q 'wait --for=delete pod' "$work/calls"
if grep -q ' apply \|--replicas=1\| create secret' "$work/calls"; then echo 'Started replacement before stop barrier'; exit 1; fi
if bash deploy/kubernetes.sh scale "$work/deployment" 2 > "$work/result" 2>&1; then echo 'Scale ignored stop failure'; exit 1; fi
jq -e '.workers==3' "$work/deployment/deployment.json" >/dev/null
export HELPER_KUBE_MODE=stopped
: > "$work/calls"
bash deploy/kubernetes.sh down "$work/deployment" > "$work/result" 2>&1
grep -q 'scale statefulset/worker1 --replicas=0' "$work/calls"
grep -q 'delete configmap cloud-operation' "$work/calls"
if grep -q 'delete pvc\|delete namespace' "$work/calls"; then echo 'Down destroyed data'; exit 1; fi
# Resource/startup changes must not change durable identity, including records
# saved before these optional settings were excluded from the identity.
jq '.data.identity |= (fromjson | .startupSeconds=300 | tojson)' "$work/record.json" > "$work/record.next"
mv "$work/record.next" "$work/record.json"
jq '.startupSeconds=900 | .cpuMillis=6000 | .memoryMiB=8192 | .schedulerResources={cpuMillis:250,memoryMiB:512}' \
  "$work/deployment/deployment.json" > "$work/deployment/next.json"
mv "$work/deployment/next.json" "$work/deployment/deployment.json"
bash deploy/kubernetes.sh down "$work/deployment" > "$work/result" 2>&1
cp "$work/deployment/deployment.json" "$work/original.json"
jq '.image="registry/other@sha256:0000000000000000000000000000000000000000000000000000000000000002"' \
  "$work/original.json" > "$work/deployment/deployment.json"
: > "$work/calls"
if bash deploy/kubernetes.sh down "$work/deployment" > "$work/result" 2>&1; then echo 'Accepted image identity change'; exit 1; fi
grep -q 'Deployment image, storage settings or identity changed' "$work/result"
if grep -q 'scale\| apply ' "$work/calls"; then echo 'Changed deployment before validating identity'; exit 1; fi
cp "$work/original.json" "$work/deployment/deployment.json"
bash deploy/kubernetes.sh show "$work/deployment" > "$work/shown.json"
cmp "$work/deployment/deployment.json" "$work/shown.json"
: > "$work/calls"
if bash deploy/kubernetes.sh scale "$work/deployment" invalid > "$work/result" 2>&1; then echo 'Accepted invalid worker count'; exit 1; fi
[[ ! -s "$work/calls" ]]
# Scale starts the requested workers only after the old generation has stopped,
# and publishes matching mailbox membership. A later scale to zero retires them.
bash deploy/kubernetes.sh scale "$work/deployment" 2 > "$work/result" 2>&1
jq -e '.workers==2' "$work/deployment/deployment.json" >/dev/null
jq -e 'map(.worker)==["worker1","worker2"]' "$work/membership.json" >/dev/null
jq -e 'all(.cpus==6 and .memoryMiB==8192)' "$work/membership.json" >/dev/null
jq -e '[.items[]|select(.kind=="StatefulSet" and .metadata.name!="scheduler")|.spec.template.spec.containers[0].resources]|all(.requests.cpu=="6000m" and .limits.memory=="8192Mi")' "$work/deployment/resources.json" >/dev/null
awk '/wait --for=delete pod/ {stopped=1} /--replicas=1/ {if (!stopped) exit 1}' "$work/calls"
grep -Fq 'scale statefulset/worker2 --replicas=1' "$work/calls"
: > "$work/calls"
bash deploy/kubernetes.sh scale "$work/deployment" 0 > "$work/result" 2>&1
jq -e '.workers==0' "$work/deployment/deployment.json" >/dev/null
jq -e '.==[]' "$work/membership.json" >/dev/null
grep -q 'pool-stopped .*worker1 1' "$work/calls"
if grep -q 'statefulset/worker.*--replicas=1' "$work/calls"; then echo 'Started a worker after scaling to zero'; exit 1; fi
bash deploy/kubernetes.sh connect "$work/deployment" 18080 > "$work/result"
grep -q 'http://127.0.0.1:18080' "$work/result"
grep -q 'port-forward --address 127.0.0.1 service/cloud-api 18080:8080' "$work/calls"
if bash deploy/kubernetes.sh connect "$work/deployment" 65536 > "$work/result" 2>&1; then echo 'Accepted invalid port'; exit 1; fi
if bash deploy/kubernetes.sh clean "$work/deployment" > "$work/result" 2>&1; then echo 'Clean did not require confirmation'; exit 1; fi
# Clean uses the same stop barrier and ownership validation as up/down.
export HELPER_KUBE_MODE=stop-failed
: > "$work/calls"
if bash deploy/kubernetes.sh clean "$work/deployment" --yes > "$work/result" 2>&1; then echo 'Clean ignored stop failure'; exit 1; fi
if grep -q 'delete namespace' "$work/calls"; then echo 'Deleted active deployment'; exit 1; fi
export HELPER_KUBE_MODE=retain
: > "$work/calls"
if bash deploy/kubernetes.sh clean "$work/deployment" --yes > "$work/result" 2>&1; then echo 'Reported retained disks as deleted'; exit 1; fi
if grep -q 'delete namespace' "$work/calls"; then echo 'Deleted namespace with retained disks'; exit 1; fi
# A PV deletion timeout must fail, but a later clean can resume without a namespace.
export HELPER_KUBE_MODE=pv-timeout
if bash deploy/kubernetes.sh clean "$work/deployment" --yes > "$work/result" 2>&1; then echo 'Ignored disk deletion timeout'; exit 1; fi
jq -e '.==["test-disk"]' "$work/deployment/cleanup-volumes.json" >/dev/null
[[ -f "$work/namespace-deleted" ]]
if bash deploy/kubernetes.sh up "$work/deployment" > "$work/result" 2>&1; then echo 'Reused a cleaned deployment'; exit 1; fi
export HELPER_KUBE_MODE=pv-error
if bash deploy/kubernetes.sh clean "$work/deployment" --yes > "$work/result" 2>&1; then echo 'Ignored failed PV lookup'; exit 1; fi
export HELPER_KUBE_MODE=stopped
bash deploy/kubernetes.sh clean "$work/deployment" --yes > "$work/result" 2>&1
[[ -f "$work/pv-deleted" ]]
bash deploy/kubernetes.sh clean "$work/deployment" --yes > "$work/result" 2>&1
# Resume deletion while the namespace itself is still terminating.
rm "$work/namespace-deleted"
jq '.metadata.deletionTimestamp="2026-01-01T00:00:00Z"' "$work/namespace.json" > "$work/ns.next"
mv "$work/ns.next" "$work/namespace.json"
bash deploy/kubernetes.sh clean "$work/deployment" --yes > "$work/result" 2>&1
[[ -f "$work/namespace-deleted" ]]
printf 'Kubernetes stop and durable identity contracts passed.\n'
