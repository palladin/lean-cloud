#!/usr/bin/env bash
# A real GitHub request submitted through the ordinary HTTP cloud client.
set -euo pipefail
app=$(cd "$(dirname "$0")" && pwd -P)
root=$(cd "$app/../.." && pwd -P)
[[ $# == 1 ]] || { echo 'Usage: test-deployment.sh IMAGE' >&2; exit 1; }
image=$1
mkdir -p "$root/.lean-cloud"
test_dir=$(mktemp -d "$root/.lean-cloud/build-integration.XXXXXX")
deployment="$test_dir/deployment"
name="build-test-$$"
cleanup() {
  local status=$?
  if [[ -f "$deployment/deployment.json" ]]; then
    if ! bash "$root/deploy/local.sh" clean "$deployment" --yes > "$test_dir/cleanup.log" 2>&1; then
      echo "Cleanup failed; see $test_dir/cleanup.log" >&2
      exit 1
    fi
  fi
  echo "Test logs: $test_dir (temporary deployment removed)"
  exit "$status"
}
trap cleanup EXIT
cli() { LEAN_CLOUD_HOME="$test_dir/client" "$root/.lake/build/bin/lean_cloud" "$@"; }
compose() { docker compose -p "$name" -f "$deployment/compose.json" "$@"; }
bash "$root/deploy/local.sh" init "$deployment" "$image" "$name" 3 0 > "$test_dir/deploy.log" 2>&1
bash "$root/deploy/local.sh" up "$deployment" >> "$test_dir/deploy.log" 2>&1
address=$(compose port scheduler 8080)
cli connect build-test "http://$address" --token-file "$deployment/client.token" > "$test_dir/connect.log"
cli programs > "$test_dir/programs.log"
before=$(compose ps -q | sort)
cli run lean-build --input "$app/example.json" --id modules
ready=false
for ((attempt=0; attempt<300; attempt++)); do
  if cli result modules > "$test_dir/report.json" 2> "$test_dir/pending.log" &&
      jq -e 'type == "object" and has("success")' "$test_dir/report.json" >/dev/null 2>&1; then
    ready=true; break
  fi
  sleep 1
done
compose logs --no-color > "$test_dir/containers.log" 2>&1
[[ $ready == true ]] || { echo 'Timed out waiting for build' >&2; exit 1; }
if ! jq -e '.success == true and .build.status == "built" and .build.artifacts != null and
    .toolchain == "leanprover/lean4:v4.35.0" and (.modules | length > 2) and
    all(.modules[]; .status == "built")' "$test_dir/report.json" >/dev/null; then
  cat "$test_dir/report.json" >&2
  exit 1
fi
jq '.build.artifacts' "$test_dir/report.json" > "$test_dir/ref.json"
bash "$app/local-files.sh" "$deployment" "$test_dir/ref.json" > "$test_dir/artifacts.json"
jq -e 'any(.[]; .path | endswith("Batteries/Data/Nat/Bisect.olean"))' "$test_dir/artifacts.json" >/dev/null
cli inspect modules > "$test_dir/inspect.log"
cli watch modules --once > "$test_dir/watch.log"
cli logs modules > "$test_dir/logs.log"
[[ $(compose ps -q | sort) == "$before" ]] || { echo 'Submission changed containers' >&2; exit 1; }
echo 'PASS GitHub source checkout, parallel module jobs, build artifacts and HTTP monitoring'
