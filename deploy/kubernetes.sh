#!/usr/bin/env bash
# Usage: kubernetes.sh render|up|down DIR | connect DIR [PORT]
# DIR contains deployment.json and storage.json. See deploy/README.md.
set -euo pipefail
assets=$(cd "$(dirname "$0")" && pwd -P)
source "$assets/common.sh"
need jq
[[ $# == 2 || ( $# == 3 && $1 == connect ) ]] || fail 'Usage: deploy/kubernetes.sh render|up|down DIR | connect DIR [PORT]'
command=$1; directory=$(absolute_dir "$2"); spec="$directory/deployment.json"
private_dir "$directory"
name=$(jq -er .name "$spec"); namespace=$(jq -er .namespace "$spec"); context=$(jq -er .context "$spec")
identifier "$name"; identifier "$namespace"
workers=$(jq -er .workers "$spec"); number "$workers"
startup=$(jq -er '.startupSeconds // 300' "$spec"); number "$startup"
(( startup >= 5 && startup <= 3600 )) || fail 'startupSeconds must be between 5 and 3600'
jq -e '.image|test("@sha256:[a-f0-9]{64}$")' "$spec" >/dev/null || fail 'Use an immutable registry image digest'
jq -e '[.diskGiB,.cpuMillis,.memoryMiB]|all(type=="number" and .>0 and floor==.)' "$spec" >/dev/null || fail 'Invalid resource sizes'
jq -e '(.schedulerResources // {}) | type=="object" and (keys|all(.=="cpuMillis" or .=="memoryMiB")) and (values|all(type=="number" and .>0 and floor==.))' "$spec" >/dev/null || fail 'Invalid scheduler resources'
kube() { kubectl --context "$context" --namespace "$namespace" --request-timeout=30s "$@"; }
roles() { printf 'scheduler\n'; for ((i=1;i<=workers;i++)); do printf 'worker%s\n' "$i"; done; }
if [[ "$command" == render ]]; then
  jq -f "$assets/kubernetes/resources.jq" "$spec" > "$directory/resources.json"
  printf 'Wrote %s/resources.json (no credentials; no cluster changes).\n' "$directory"
  exit
fi
need kubectl; need shasum
if [[ "$command" == connect ]]; then
  port=${3:-8080}; number "$port"
  (( port > 0 && port < 65536 )) || fail 'Invalid local port'
  printf 'In cloud CLI: connect %s http://127.0.0.1:%s --token-file "%s/client.token"\n' "$name" "$port" "$directory"
  exec kubectl --context "$context" --namespace "$namespace" port-forward --address 127.0.0.1 service/cloud-api "$port:8080"
fi
[[ "$command" == up || "$command" == down ]] || fail 'Unknown Kubernetes operation'
ns=$(kube get namespace "$namespace" --ignore-not-found -o json)
if [[ -z "$ns" ]]; then
  [[ "$command" == up ]] || fail 'Namespace is absent'
  jq -f "$assets/kubernetes/resources.jq" "$spec" | jq '.items[]|select(.kind=="Namespace")' | kube create -f - >/dev/null
else
  jq -e --arg name "$name" '.metadata.labels["lean-cloud/deployment"]==$name and .metadata.labels["app.kubernetes.io/managed-by"]=="lean-cloud"' <<< "$ns" >/dev/null || fail 'Namespace is not owned by this deployment'
fi
# Non-expiring cluster lock serializes operators, including different machines.
kube create configmap cloud-operation --from-literal="operation=$command" >/dev/null || fail 'Deployment operation is locked; verify the previous operator has stopped before removing cloud-operation.'
trap 'kube delete configmap cloud-operation --wait=true >/dev/null' EXIT
storage_hash=$(jq -Sc . "$directory/storage.json" | shasum -a 256 | cut -d " " -f 1)
identity_filter='del(.workers,.cpuMillis,.memoryMiB,.schedulerResources,.startupSeconds)'
identity=$(jq -Sc "$identity_filter" "$spec")
record=$(kube get configmap cloud-deployment --ignore-not-found -o json)
if [[ -n "$record" ]]; then
  recorded_identity=$(jq -r '.data.identity' <<< "$record" | jq -Sc "$identity_filter")
  [[ "$recorded_identity" == "$identity" ]] || fail 'Deployment image, storage settings or identity changed. Use a new namespace.'
  [[ $(jq -r '.data.storage' <<< "$record") == "${storage_hash}" ]] || fail 'Blob storage changed; use a new deployment.'
  while IFS= read -r claim; do
    pvc=$(jq -r .name <<< "$claim"); uid=$(jq -r .uid <<< "$claim")
    actual=$(kube get pvc "$pvc" -o json)
    [[ $(jq -r .metadata.uid <<< "$actual") == "$uid" ]] || fail "Durable claim replaced: $pvc"
  done < <(jq -r '.data.claims|fromjson|.[]|@json' <<< "$record")
fi
previous=$(kube get statefulsets -l "lean-cloud/deployment=$name" -o json | jq -r '.items[].metadata.name')
# Stop scheduler first. A timeout aborts; never force-delete an unreachable pod.
if [[ -n "$previous" ]]; then
  kube scale statefulset/scheduler --replicas=0
  while IFS= read -r role; do [[ "$role" == scheduler ]] || kube scale "statefulset/$role" --replicas=0; done <<< "$previous"
  kube wait --for=delete pod -l "lean-cloud/deployment=$name" --timeout=180s
fi
[[ "$command" == up ]] || exit 0
need openssl
for token in client internal; do
  [[ -s "$directory/$token.token" ]] || secret > "$directory/$token.token"
done
jq -n --slurpfile spec "$spec" --slurpfile storage "$directory/storage.json" \
  --rawfile client "$directory/client.token" --rawfile internal "$directory/internal.token" '
  $spec[0] as $c | {client:{deployment:$c.name,image:$c.image,token:($client|rtrimstr("\n"))},
  scheduler:{database:"/data/scheduler.sqlite",assignmentMs:30000},blobs:$storage[0],
  mailboxes:{scheduler:{host:"scheduler",port:8080,token:($internal|rtrimstr("\n"))},workers:[range(1;$c.workers+1)|{worker:"worker\(.)",endpoint:{host:"worker\(.)",port:8080,token:($internal|rtrimstr("\n"))}}]}}
  ' > "$directory/config.json"
# Save identity before allocating volumes so failed setup cannot be claimed by another image.
claims=$(if [[ -n "$record" ]]; then jq -r '.data.claims' <<< "$record"; else printf '[]'; fi)
record_identity() {
  kube create configmap cloud-deployment --from-literal="identity=$identity" \
    --from-literal="storage=${storage_hash}" --from-literal="claims=$claims" \
    --dry-run=client -o json | kube apply -f - >/dev/null
}
record_identity
jq -f "$assets/kubernetes/resources.jq" "$spec" > "$directory/resources.json"
while IFS= read -r role; do
  pvc=$(kube get pvc "state-$role-0" --ignore-not-found -o json)
  if [[ -n "$pvc" ]]; then
    jq -e --arg name "$name" --arg role "$role" '.metadata.labels["lean-cloud/deployment"]==$name and .metadata.labels["lean-cloud/role"]==$role' <<< "$pvc" >/dev/null || fail "Claim state-$role-0 belongs to another node"
  fi
done < <(roles)
kube apply -f "$directory/resources.json"
claims=$(kube get pvc -l "lean-cloud/deployment=$name" -o json | jq '[.items[]|{name:.metadata.name,uid:.metadata.uid}]')
record_identity
kube create secret generic cloud-config --from-file="config.json=$directory/config.json" --dry-run=client -o json | kube apply -f - >/dev/null
ready() {
  kube scale "statefulset/$1" --replicas=1
  kube wait --for=create "pod/$1-0" --timeout=180s
  kube wait --for=condition=Ready "pod/$1-0" --timeout="${startup}s"
}
ready scheduler
jq -c .mailboxes.workers "$directory/config.json" | kube exec -i scheduler-0 -- cloud-app pool-configure /etc/lean-cloud/config.json >/dev/null
membership=$(kube exec scheduler-0 -- cloud-app pool-workers /etc/lean-cloud/config.json)
generation=$(jq -er .generation <<< "$membership")
while IFS= read -r role; do
  [[ -z "$role" || "$role" == scheduler ]] && continue
  if ! roles | grep -Fxq "$role"; then
    kube exec scheduler-0 -- cloud-app pool-stopped /etc/lean-cloud/config.json "$role" "$generation" >/dev/null
  fi
done <<< "$previous"
while IFS= read -r role; do [[ "$role" == scheduler ]] || ready "$role"; done < <(roles)
printf 'Ready. Run deploy/kubernetes.sh connect "%s" in another terminal.\n' "$directory"
