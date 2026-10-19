#!/usr/bin/env bash
# Inspectable Kubernetes data import, independent of the cloud console.
set -euo pipefail
app=$(cd "$(dirname "$0")" && pwd -P)
usage() { echo 'Usage: cluster.sh render|start|status|logs|result|retry DEPLOYMENT DIRECTORY | clean DEPLOYMENT DIRECTORY --yes' >&2; }
[[ $# -ge 3 ]] || { usage; exit 2; }
command=$1; deployment=$(cd "$2" && pwd -P)
case "$command" in
  render|start|status|logs|result|retry) [[ $# == 3 ]] || { usage; exit 2; } ;;
  clean) [[ $# == 4 && $4 == --yes ]] || { usage; exit 2; } ;;
  *) usage; exit 2 ;;
esac
umask 077
mkdir -p "$3"
directory=$(cd "$3" && pwd -P)
spec="$deployment/deployment.json"
owner=$(printf '%s' "$directory" | openssl dgst -sha256 -r | cut -c 1-32)
options=(--context "$(jq -er .context "$spec")" --namespace "$(jq -er .namespace "$spec")")
kubeconfig=$(jq -r '.kubeconfig // empty' "$spec")
[[ -z "$kubeconfig" ]] || options+=(--kubeconfig "$kubeconfig")
kube() { kubectl "${options[@]}" --request-timeout=30s "$@"; }
if [[ "$command" == render ]]; then
  [[ ! -f "$directory/ingest.json" ]] || { echo 'Already rendered. Reuse this directory, or choose a new one.' >&2; exit 1; }
  jq -e '.image|test("@sha256:[a-f0-9]{64}$")' "$spec" >/dev/null
  jq --arg owner "$owner" '. + {owner:$owner}' "$spec" | jq -f "$app/ingest.jq" > "$directory/ingest.json"
  cp "$app/snapshot.json" "$app/ingest.sh" "$directory/"
  # Bind this output directory to the deployment identity; no tokens are copied.
  jq -S '{name,namespace,context,kubeconfig,image,storageClass}' "$spec" > "$directory/target.json"
  echo "Rendered $directory/ingest.json. Review it, then use 'start'. No resources created."
  exit
fi
jq -S '{name,namespace,context,kubeconfig,image,storageClass}' "$spec" > "$directory/target.next"
cmp "$directory/target.json" "$directory/target.next" >/dev/null || {
  echo 'Deployment changed; use the original deployment or render a new import.' >&2; exit 1;
}
rm "$directory/target.next"
# Serialize lifecycle changes, including commands issued from another machine.
# In particular, cleanup must not delete a disk underneath a new retry.
case "$command" in
  start|retry|clean)
    kube create configmap wiki-import-operation --from-literal="operation=$command" >/dev/null || {
      echo 'Import operation is locked. Check the previous operator before removing wiki-import-operation.' >&2; exit 1;
    }
    trap 'kube delete configmap wiki-import-operation --ignore-not-found --wait=true >/dev/null' EXIT
    ;;
esac
# Fixed names make concurrent imports explicit. Never take over another import.
for resource in job/wiki-import pvc/wiki-import configmap/wiki-import; do
  existing=$(kube get "$resource" --ignore-not-found -o json)
  [[ -z "$existing" ]] || jq -e --arg owner "$owner" '.metadata.labels["lean-cloud/wiki-ingest"]==$owner' <<< "$existing" >/dev/null || {
    echo "Another import owns $resource; use its directory." >&2; exit 1;
  }
done
start_import() {
    if [[ -n $(kube get job/wiki-import --ignore-not-found -o name) ]]; then
      echo 'Import already started. Use status/logs/result, or retry after failure.'; return
    fi
    # No old job is running. Refresh the mounted files so a retry uses the
    # inspected script/snapshot, rather than silently reusing an old ConfigMap.
    kube create configmap wiki-import --from-file="$directory/ingest.sh" --from-file="$directory/snapshot.json" \
      --dry-run=client -o json | jq --arg owner "$owner" '.metadata.labels={"lean-cloud/wiki-ingest":$owner}' | kube apply -f -
    if [[ -z $(kube get pvc/wiki-import --ignore-not-found -o name) ]]; then
      jq '.items[]|select(.kind=="PersistentVolumeClaim")' "$directory/ingest.json" | kube create -f -
    fi
    jq '.items[]|select(.kind=="Job")' "$directory/ingest.json" | kube create -f -
    echo "Import started. Use 'logs' for progress, then 'result' to save prepare.json."
}
case "$command" in
  start) start_import ;;
  status) kube get jobs,pods,pvc -l "lean-cloud/wiki-ingest=$owner" -o wide ;;
  logs) kubectl "${options[@]}" logs --follow job/wiki-import ;;
  result)
    kube get job/wiki-import -o json | jq -e '.status.succeeded==1' >/dev/null || {
      echo 'Import is not complete. Check status/logs.' >&2; exit 1;
    }
    kube logs job/wiki-import | sed -n 's/^WIKI_PREPARE_REQUEST=//p' | \
      jq -se 'if length==1 and (.[0].source|type=="object") then .[0] else error("Missing import result") end' > "$directory/prepare.next"
    mv "$directory/prepare.next" "$directory/prepare.json"
    echo "Saved $directory/prepare.json"
    ;;
  retry)
    kube get job/wiki-import -o json | jq -e '.status.conditions|any(.type=="Failed" and .status=="True")' >/dev/null || {
      echo 'Only a failed import may be retried. Check status/logs.' >&2; exit 1;
    }
    kube delete job/wiki-import --cascade=foreground --wait=true --timeout=180s
    start_import
    ;;
  clean)
    # Stop the writer before removing its disk. The imported shared blobs stay.
    volume=$(kube get pvc/wiki-import --ignore-not-found -o json | jq -r '.spec.volumeName // empty')
    if [[ -n "$volume" ]]; then
      kube get pv "$volume" -o json | jq -e '.spec.persistentVolumeReclaimPolicy=="Delete"' >/dev/null || {
        echo 'The ingest disk has a Retain policy; arrange disk cleanup before deleting its claim.' >&2; exit 1;
      }
      printf '%s\n' "$volume" > "$directory/cleanup-volume"
    fi
    kube delete job/wiki-import --ignore-not-found --cascade=foreground --wait=true --timeout=180s
    kube delete pvc/wiki-import configmap/wiki-import --ignore-not-found --wait=true --timeout=300s
    if [[ -f "$directory/cleanup-volume" ]]; then
      volume=$(cat "$directory/cleanup-volume")
      [[ -z $(kube get pv "$volume" --ignore-not-found -o name) ]] || kube wait --for=delete "pv/$volume" --timeout=300s
    fi
    echo 'Removed import job and scratch disk. Imported blobs and local request files remain.'
    ;;
esac
