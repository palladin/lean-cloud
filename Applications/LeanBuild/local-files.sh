#!/usr/bin/env bash
set -euo pipefail
[[ $# == 2 ]] || { echo 'Usage: local-files.sh DEPLOYMENT FILE_REF_JSON' >&2; exit 1; }
directory=$(cd "$1" && pwd -P)
input=$2
name=$(jq -er .name "$directory/deployment.json")
compose() { docker compose -p "$name" -f "$directory/compose.json" "$@"; }
workspace=$(compose exec -T scheduler mktemp -d /tmp/build-files.XXXXXX)
cleanup() { compose exec -T scheduler rm -rf "$workspace" >/dev/null; }
trap cleanup EXIT
compose cp "$input" "scheduler:$workspace/ref.json" >/dev/null
compose exec -T scheduler cloud-app files download /etc/lean-cloud/config.json "$workspace/ref.json" -
