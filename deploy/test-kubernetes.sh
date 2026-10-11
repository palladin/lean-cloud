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
  *' get namespace '*) cat "$HELPER_KUBE_WORK/namespace.json" ;;
  *' get configmap cloud-deployment '*) cat "$HELPER_KUBE_WORK/record.json" ;;
  *' create configmap cloud-operation '*|*' delete configmap cloud-operation '*) ;;
  *' get pvc state-scheduler-0 '*)
    if [[ "$HELPER_KUBE_MODE" == replaced ]]; then printf '{"metadata":{"uid":"replacement"}}'
    else printf '{"metadata":{"uid":"original"}}'; fi ;;
  *' get statefulsets '*) printf '{"items":[{"metadata":{"name":"scheduler"}},{"metadata":{"name":"worker1"}}]}' ;;
  *' scale statefulset/'*) ;;
  *' port-forward --address 127.0.0.1 service/cloud-api '*) ;;
  *' wait --for=delete pod '*) [[ "$HELPER_KUBE_MODE" != stop-failed ]] ;;
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
export HELPER_KUBE_MODE=stopped
: > "$work/calls"
bash deploy/kubernetes.sh down "$work/deployment" > "$work/result" 2>&1
grep -q 'scale statefulset/worker1 --replicas=0' "$work/calls"
grep -q 'delete configmap cloud-operation' "$work/calls"
if grep -q 'delete pvc\|delete namespace' "$work/calls"; then echo 'Down destroyed data'; exit 1; fi
bash deploy/kubernetes.sh connect "$work/deployment" 18080 > "$work/result"
grep -q 'http://127.0.0.1:18080' "$work/result"
grep -q 'port-forward --address 127.0.0.1 service/cloud-api 18080:8080' "$work/calls"
if bash deploy/kubernetes.sh connect "$work/deployment" 65536 > "$work/result" 2>&1; then echo 'Accepted invalid port'; exit 1; fi
printf 'Kubernetes stop and durable identity contracts passed.\n'
