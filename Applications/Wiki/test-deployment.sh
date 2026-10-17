#!/usr/bin/env bash
# Exercise the registered workflows through HTTP on three real worker processes.
set -euo pipefail
app=$(cd "$(dirname "$0")" && pwd -P)
root=$(cd "$app/../.." && pwd -P)
[[ $# == 1 ]] || { echo 'Usage: test-deployment.sh IMAGE' >&2; exit 2; }
mkdir -p "$root/.lean-cloud"
test_dir=$(mktemp -d "$root/.lean-cloud/wiki-integration.XXXXXX")
deployment="$test_dir/deployment"
name="wiki-check-$$"
cleanup() {
  local status=$?
  if [[ -f "$deployment/deployment.json" ]]; then
    if ! bash "$root/deploy/local.sh" clean "$deployment" --yes > "$test_dir/cleanup.log" 2>&1; then
      echo "Cleanup failed; see $test_dir/cleanup.log" >&2; exit 1
    fi
  fi
  echo "Test logs: $test_dir (temporary deployment removed)"
  exit "$status"
}
trap cleanup EXIT
cli() { LEAN_CLOUD_HOME="$test_dir/client" "$root/.lake/build/bin/lean_cloud" "$@"; }
compose() { docker compose -p "$name" -f "$deployment/compose.json" "$@"; }
result() {
  for ((attempt=0; attempt<120; attempt++)); do
    if cli result "$1" > "$test_dir/$1.json" 2> "$test_dir/pending.log" &&
        jq -e 'type == "object"' "$test_dir/$1.json" >/dev/null 2>&1; then return; fi
    sleep 1
  done
  compose logs --no-color > "$test_dir/containers.log" 2>&1
  echo "Timed out waiting for $1" >&2; return 1
}
bash "$root/deploy/local.sh" init "$deployment" "$1" "$name" 3 0 > "$test_dir/deploy.log" 2>&1
bash "$root/deploy/local.sh" up "$deployment" >> "$test_dir/deploy.log" 2>&1
address=$(compose port scheduler 8080)
cli connect wiki-test "http://$address" --token-file "$deployment/client.token" > "$test_dir/connect.log"
cli programs > "$test_dir/programs.log"
before=$(compose ps -q | sort)
awk 'BEGIN { for (i=0; i<100000; i++) pad=pad "padding " }
  { sub(/<text \/>/, "<text> </text>"); sub(/<\/text>/, " " pad "</text>"); print }' \
  "$app/fixtures/tiny.xml" > "$test_dir/three-shards.xml"
bash "$app/local-files.sh" "$deployment" import-xml "$test_dir/three-shards.xml" "$test_dir/import.json"
jq '.shardBytes=1048576' "$test_dir/import.json" > "$test_dir/prepare-input.json"
cli run wiki-prepare --input "$test_dir/prepare-input.json" --id prepare
result prepare
jq -e '.articles == 3 and .shards == 3' "$test_dir/prepare.json" >/dev/null
jq '{dataset, vocabulary:["proof","theorem","algorithm","computer"]}' "$test_dir/prepare.json" > "$test_dir/count-input.json"
cli run wiki-count --input "$test_dir/count-input.json" --id counts
result counts
jq -e '.articles == 3 and [.counts[].occurrences] == [4,1,2,1] and [.counts[].articles] == [2,1,2,1]' "$test_dir/counts.json" >/dev/null
jq '{dataset,pattern:"π proof"}' "$test_dir/prepare.json" > "$test_dir/grep-input.json"
cli run wiki-grep --input "$test_dir/grep-input.json" --id search
result search
jq -e '.articles == 3 and .matched == 1' "$test_dir/search.json" >/dev/null
jq .results "$test_dir/search.json" > "$test_dir/ref.json"
bash "$app/local-files.sh" "$deployment" download "$test_dir/ref.json" "$test_dir/matches.json"
jq '.parts[] | select(.matched > 0) | .file' "$test_dir/matches.json" > "$test_dir/ref.json"
bash "$app/local-files.sh" "$deployment" download "$test_dir/ref.json" "$test_dir/hits.jsonl"
jq -e '.id == 2 and .title == "Computers" and .length == 8' "$test_dir/hits.jsonl" >/dev/null
cli inspect counts > "$test_dir/inspect.log"
cli watch counts --once > "$test_dir/watch.log"
[[ $(compose ps -q | sort) == "$before" ]] || { echo 'Submission changed containers' >&2; exit 1; }
echo 'PASS Wiki HTTP submission, preparation, counting, searching, artifact downloads and monitoring'
