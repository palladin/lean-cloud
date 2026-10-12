#!/usr/bin/env bash
set -euo pipefail
app=$(cd "$(dirname "$0")" && pwd -P)
root=$(cd "$app/../.." && pwd -P)
[[ $# -le 2 ]] || { echo 'Usage: build.sh [IMAGE [SOURCE_LEAN_VERSION]]' >&2; exit 1; }
image=${1:-lean-cloud-verify:dev}
version=${2:-$(sed 's/leanprover\/lean4:v//' "$app/lean-toolchain")}
[[ $version =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] || { echo 'Expected a stable Lean release' >&2; exit 1; }
bash "$root/deploy/build.sh" "$app" lean-cloud-verify-app:dev
docker build --build-arg APPLICATION_IMAGE=lean-cloud-verify-app:dev \
  --build-arg "VERIFY_LEAN_VERSION=$version" -t "$image" "$app"
