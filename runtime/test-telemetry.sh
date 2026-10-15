#!/usr/bin/env bash
# Linux kernel-format reader tests; no Docker daemon or cgroup permissions needed.
set -euo pipefail
cd "$(dirname "$0")"
if [[ $(uname -s) != Linux ]]; then
  printf 'Native telemetry reader tests require Linux.\n'
  exit 0
fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
prefix=$(lean --print-prefix)
# Only the tested readers are reachable; discard the unused Lean FFI entrypoints.
cc -O2 -Wall -Wextra -Werror -ffunction-sections -fdata-sections \
  -I "$prefix/include" native/telemetry_test.c -Wl,--gc-sections -o "$work/telemetry-test"
"$work/telemetry-test"
