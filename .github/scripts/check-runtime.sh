#!/usr/bin/env bash
set -euo pipefail

mkdir -p .lean-cloud/ci-runtime-logs
driver=.lake/build/bin/cloud_console_tests
if [[ $# == 0 || ! -x "$driver" ]]; then
  echo 'Runtime checks require a built test driver and at least one suite.' >&2
  exit 1
fi
pids=()
suites=()
for suite in "$@"; do
  case "$suite" in
    lifecycle|pool|scaling|chaos|maintenance) ;;
    *) echo "Unknown runtime suite: $suite" >&2; exit 1 ;;
  esac
done

# Every invocation allocates its own deployment, catalog, containers and volumes.
# The executable is already built; concurrent suites must not run Lake builds.
trap 'trap - INT TERM; kill "${pids[@]}" 2>/dev/null || true; wait || true; exit 130' INT TERM
for suite in "$@"; do
  echo "Starting runtime $suite"
  # Network chaos must outlast real assignment leases before asserting recovery.
  limit=360
  if [[ "$suite" == chaos ]]; then limit=480; fi
  timeout --kill-after=15s "${limit}s" "$driver" "--$suite-only" \
    > ".lean-cloud/ci-runtime-logs/$suite.log" 2>&1 &
  pids+=("$!")
  suites+=("$suite")
done

failed=0
for i in "${!pids[@]}"; do
  if wait "${pids[$i]}"; then
    echo "Runtime ${suites[$i]} passed"
  else
    status=$?
    echo "::error::Runtime ${suites[$i]} failed (exit $status; 124 means the suite time limit expired)"
    tail -n 80 ".lean-cloud/ci-runtime-logs/${suites[$i]}.log" || true
    failed=1
  fi
done
exit "$failed"
