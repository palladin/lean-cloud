#!/usr/bin/env bash
# Uses a fresh local deployment and always tears down its own containers/volumes.
set -euo pipefail
app=$(cd "$(dirname "$0")" && pwd -P)
root=$(cd "$app/../.." && pwd -P)
[[ $# == 1 ]] || { echo 'Usage: test-deployment.sh IMAGE' >&2; exit 1; }
image=$1
mkdir -p "$root/.lean-cloud"
test_dir=$(mktemp -d "$root/.lean-cloud/sat-integration.XXXXXX")
deployment="$test_dir/deployment"
name="sat-check-$$"
cleanup() {
  local run_status=$?
  if [[ -f "$deployment/deployment.json" ]]; then
    if ! bash "$root/deploy/local.sh" clean "$deployment" --yes > "$test_dir/cleanup.log" 2>&1; then
      echo "Cleanup failed; inspect $test_dir/cleanup.log" >&2
      exit 1
    fi
  fi
  echo "Test logs: $test_dir (temporary deployment removed)"
  exit "$run_status"
}
trap cleanup EXIT
cli() { LEAN_CLOUD_HOME="$test_dir/client" "$root/.lake/build/bin/lean_cloud" "$@"; }
compose() { docker compose -p "$name" -f "$deployment/compose.json" "$@"; }
wait_result() {
  local id=$1
  for ((attempt=0; attempt<120; attempt++)); do
    if cli result "$id" > "$test_dir/$id.json" 2> "$test_dir/$id.pending" &&
        jq -e 'type == "object" and has("outcome")' "$test_dir/$id.json" >/dev/null 2>&1; then return; fi
    sleep 1
  done
  echo "Timed out waiting for $id" >&2
  compose logs --no-color > "$test_dir/containers.log" 2>&1
  return 1
}
bash "$root/deploy/local.sh" configure "$deployment" "$image" "$name" 3 0 > "$test_dir/deploy.log" 2>&1
jq '.cpuMillis=2000' "$deployment/deployment.json" > "$deployment/deployment.next"
mv "$deployment/deployment.next" "$deployment/deployment.json"
# scale re-renders the edited resource policy before starting the three nodes.
bash "$root/deploy/local.sh" scale "$deployment" 3 >> "$test_dir/deploy.log" 2>&1
address=$(compose port scheduler 8080)
cli connect sat-test "http://$address" --token-file "$deployment/client.token" > "$test_dir/connect.log"
cli programs > "$test_dir/programs.log"
before=$(compose ps -q | sort)
bash "$app/local-files.sh" "$deployment" prepare "$app/examples/pigeonhole.cnf" > "$test_dir/pigeons-input.json"
bash "$app/local-files.sh" "$deployment" prepare "$app/examples/sat.cnf" > "$test_dir/sat-input.json"
jq ' .depth=4 | .splitDepth=2 | .cubesPerJob=4 | .seconds=20 | .verifySeconds=20 ' "$test_dir/pigeons-input.json" > "$test_dir/parameters.json"
cli run cube-and-conquer --input "$test_dir/parameters.json" --id pigeons
cli run cube-and-conquer --input "$test_dir/sat-input.json" --id sat
wait_result pigeons
wait_result sat
jq -e '.outcome == "unsat" and .totalCubes > 1 and .solvedCubes == .totalCubes' "$test_dir/pigeons.json" >/dev/null
jq -e '.outcome.sat.model.manifest.key | length > 0' "$test_dir/sat.json" >/dev/null
for id in pigeons sat; do
  bash "$app/local-files.sh" "$deployment" verify "$test_dir/$id.json" > "$test_dir/$id.verified"
  jq '.bundle' "$test_dir/$id.json" > "$test_dir/$id.ref.json"
  bash "$app/local-files.sh" "$deployment" download "$test_dir/$id.ref.json" > "$test_dir/$id.bundle.json"
done
jq -e '.request.cnf.manifest.key and ([.results[].answer.unsat.proof.manifest.key]|length>1)' "$test_dir/pigeons.bundle.json" >/dev/null
jq '.outcome.sat.model' "$test_dir/sat.json" > "$test_dir/model.ref.json"
bash "$app/local-files.sh" "$deployment" download "$test_dir/model.ref.json" > "$test_dir/model.sat"
rg -q '^v .*0' "$test_dir/model.sat"
cli ps > "$test_dir/ps.log"
cli inspect pigeons > "$test_dir/inspect.log"
# At least two nested parallel levels must execute on the real runtime.
rg -q '0:[0-9]+/[0-9]+:[0-9]+/[0-9]+:' "$test_dir/inspect.log"
cli watch pigeons --once > "$test_dir/watch.log"
cli logs pigeons > "$test_dir/logs.log"
[[ $(compose ps -q | sort) == "$before" ]] || { echo 'Submission changed containers' >&2; exit 1; }
cli remove sat
echo 'PASS HTTP submission, recursive distributed cubing and SAT/UNSAT, inspection/watch and stable containers'
