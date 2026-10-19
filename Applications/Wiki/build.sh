#!/usr/bin/env bash
set -euo pipefail
app=$(cd "$(dirname "$0")" && pwd -P)
root=$(cd "$app/../.." && pwd -P)
[[ $# -le 2 ]] || { echo 'Usage: build.sh [IMAGE [PLATFORM]]' >&2; exit 2; }
options=(--load)
[[ -z ${2:-} ]] || options+=(--platform "$2")
version=$(sed 's|leanprover/lean4:v||' "$app/lean-toolchain" | tr -d '\n\r')
docker buildx build "${options[@]}" --build-context "sdk=$root" --build-context "node_assets=$root/deploy" \
  --build-arg "LEAN_VERSION=$version" --build-arg APP_TARGET=cloud_app \
  --build-arg 'APP_BUILD_PACKAGES=libexpat1-dev libbz2-dev' \
  --build-arg 'APP_RUNTIME_PACKAGES=libexpat1 libbz2-1.0 bzip2 jq' \
  -f "$root/deploy/app/Dockerfile" -t "${1:-lean-cloud-wiki:dev}" "$app"
