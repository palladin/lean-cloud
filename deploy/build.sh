#!/usr/bin/env bash
# Build either this repository's demo or a registered user application.
# Images stay local until the user runs docker push.
set -euo pipefail
assets=$(cd "$(dirname "$0")" && pwd -P)
source "$assets/common.sh"
options=(--load)
if [[ ${1:-} == --platform ]]; then
  [[ $# -ge 2 ]] || fail 'Missing platform (linux/arm64 or linux/amd64)'
  [[ $2 == linux/arm64 || $2 == linux/amd64 ]] || fail 'Platform must be linux/arm64 or linux/amd64'
  options+=(--platform "$2")
  shift 2
fi
[[ $# -ge 2 && $# -le 4 ]] || fail 'Usage: deploy/build.sh [--platform linux/arm64|linux/amd64] APP_DIRECTORY IMAGE [TARGET [SDK_CHECKOUT]]'
need docker
app=$(absolute_dir "$1"); image=$2; target=${3:-cloud_app}; sdk=$(absolute_dir "${4:-$assets/..}")
version=$(sed 's|leanprover/lean4:v||' "$app/lean-toolchain" | tr -d '\n\r')
[[ "$version" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] || fail 'Use a versioned Lean toolchain'
if [[ "$app" == "$sdk" ]]; then
  docker buildx build "${options[@]}" --target worker --build-arg "LEAN_VERSION=$version" -t "$image" "$app"
else
  docker buildx build "${options[@]}" --build-context "sdk=$sdk" --build-context "node_assets=$assets" \
    --build-arg "LEAN_VERSION=$version" --build-arg "APP_TARGET=$target" \
    -f "$assets/app/Dockerfile" -t "$image" "$app"
fi
