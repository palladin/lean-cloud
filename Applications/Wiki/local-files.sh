#!/usr/bin/env bash
# File transfer helper only. Workflow submission uses the ordinary HTTP console.
set -euo pipefail
[[ $# -ge 2 ]] || { echo 'Usage: local-files.sh DEPLOYMENT import DUMP INDEX REQUEST | import-xml DUMP REQUEST | download FILE_REF OUTPUT' >&2; exit 2; }
directory=$(cd "$1" && pwd -P)
shift
name=$(jq -er .name "$directory/deployment.json")
compose() { docker compose -p "$name" -f "$directory/compose.json" "$@"; }
workspace=$(compose exec -T scheduler mktemp -d /tmp/wiki-files.XXXXXX)
cleanup() { compose exec -T scheduler rm -rf "$workspace" >/dev/null; }
trap cleanup EXIT
config=/etc/lean-cloud/config.json
case "$1" in
  import)
    [[ $# == 4 ]] || exit 2
    index=index.txt; [[ $3 != *.bz2 ]] || index=index.txt.bz2
    compose cp "$2" "scheduler:$workspace/dump.bz2" >/dev/null
    compose cp "$3" "scheduler:$workspace/$index" >/dev/null
    compose exec -T scheduler cloud-app files import "$config" "$workspace/dump.bz2" "$workspace/$index" "$workspace/request.json"
    compose cp "scheduler:$workspace/request.json" "$4" >/dev/null
    ;;
  import-xml)
    [[ $# == 3 ]] || exit 2
    dump=dump.xml; [[ $2 != *.bz2 ]] || dump=dump.xml.bz2
    compose cp "$2" "scheduler:$workspace/$dump" >/dev/null
    compose exec -T scheduler cloud-app files import-xml "$config" "$workspace/$dump" "$workspace/request.json"
    compose cp "scheduler:$workspace/request.json" "$3" >/dev/null
    ;;
  download)
    [[ $# == 3 ]] || exit 2
    compose cp "$2" "scheduler:$workspace/ref.json" >/dev/null
    compose exec -T scheduler cloud-app files download "$config" "$workspace/ref.json" "$workspace/result"
    compose cp "scheduler:$workspace/result" "$3" >/dev/null
    ;;
  *) echo 'Expected import, import-xml or download' >&2; exit 2 ;;
esac
