#!/usr/bin/env bash
# File transfer utility for the app's blob store. Runs in the existing scheduler
# container solely to use its private network and mounted storage configuration.
set -euo pipefail
[[ $# == 3 ]] || { echo 'Usage: local-files.sh DEPLOYMENT prepare|download|verify|run FILE' >&2; exit 1; }
directory=$(cd "$1" && pwd -P)
command=$2
input=$3
case "$command" in prepare|download|verify|run) ;; *) echo 'Unknown file operation' >&2; exit 1 ;; esac
name=$(jq -er .name "$directory/deployment.json")
compose() { docker compose -p "$name" -f "$directory/compose.json" "$@"; }
workspace=$(compose exec -T scheduler mktemp -d /tmp/sat-files.XXXXXX)
cleanup() { compose exec -T scheduler rm -rf "$workspace" >/dev/null; }
trap cleanup EXIT
compose cp "$input" "scheduler:$workspace/input" >/dev/null
case "$command" in
  prepare|download) compose exec -T scheduler cloud-app files "$command" /etc/lean-cloud/config.json "$workspace/input" - ;;
  verify|run) compose exec -T scheduler cloud-app files "$command" /etc/lean-cloud/config.json "$workspace/input" ;;
esac
