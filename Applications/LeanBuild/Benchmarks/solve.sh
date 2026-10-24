#!/usr/bin/env bash
set -euo pipefail

# Offline experiment; does not run a build or contact a cloud deployment.
if [[ $# -lt 2 || $# -gt 4 ]]; then
  echo "Usage: $0 schedule|barriers CASE_DIRECTORY [MILLISECONDS=60000] [THREADS=4]" >&2
  exit 2
fi
model=$1
case "$model" in schedule|barriers) ;; *) echo "Unknown model: $model" >&2; exit 2 ;; esac
case_dir=$(cd "$2" && pwd)
milliseconds=${3:-60000}
threads=${4:-4}
for value in "$milliseconds" "$threads"; do
  if [[ ! "$value" =~ ^[1-9][0-9]*$ ]]; then
    echo "Time and threads must be positive integers" >&2
    exit 2
  fi
done
script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
app_dir=$(cd "$script_dir/.." && pwd)
solver=${MINIZINC:-minizinc}
if ! command -v "$solver" >/dev/null 2>&1; then
  echo "Install MiniZinc with its open-source CP-SAT backend, or set MINIZINC to its executable." >&2
  exit 1
fi
bench="$app_dir/.lake/build/bin/plan_bench"
if [[ ! -x "$bench" ]]; then
  echo "First run: (cd '$app_dir' && lake build plan_bench)" >&2
  exit 1
fi
"$solver" --version > "$case_dir/minizinc-version.txt"
/usr/bin/time -p "$solver" --solver cp-sat -p "$threads" -r 1 -i \
  --time-limit "$milliseconds" \
  --params "num_workers:$threads cp_model_probing_level:0 symmetry_level:0 max_presolve_iterations:1" \
  --statistics --output-time --output-mode json --json-stream \
  "$script_dir/$model.mzn" "$case_dir/instance.json" \
  > "$case_dir/$model.jsonl" 2> "$case_dir/$model-timing.txt"
"$bench" evaluate "$case_dir" "$case_dir/$model.jsonl" "$case_dir/$model-report.json"
