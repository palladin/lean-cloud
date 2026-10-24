#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
  echo "Usage: $0 OUTPUT_DIRECTORY" >&2
  exit 2
fi
script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
bench="$script_dir/../.lake/build/bin/plan_bench"
mkdir -p "$1"
output=$(cd "$1" && pwd)
"$bench" test
"$bench" fixtures "$output"
for fixture in independent chain join fanout heterogeneous; do
  for model in schedule barriers; do
    "$script_dir/solve.sh" "$model" "$output/$fixture" 10000 1 > "$output/$fixture/$model-evaluation.txt"
    # Known optima for these tiny graphs. The validator already checked all
    # returned schedules; also require a candidate with the expected cost.
    jq -e --slurpfile expected "$output/$fixture/expected.json" \
      '(.candidates|length)>0 and .bestValidated.cost==$expected[0] and
       ([.candidates[].solverCost]|min)==$expected[0]' \
      "$output/$fixture/$model-report.json" >/dev/null
  done
  echo "PASS $fixture: both solver models and independent Lean validation"
done
