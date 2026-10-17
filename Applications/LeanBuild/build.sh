#!/usr/bin/env bash
set -euo pipefail
app=$(cd "$(dirname "$0")" && pwd -P)
root=$(cd "$app/../.." && pwd -P)
[[ $# -le 2 ]] || { echo 'Usage: build.sh [IMAGE [SOURCE_LEAN_VERSION]]' >&2; exit 1; }
image=${1:-lean-cloud-build:dev}
version=${2:-$(sed 's/leanprover\/lean4:v//' "$app/source-toolchain")}
if ! [[ $version =~ ^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$ ]] ||
    ! awk -F. '{ exit !($1 > 4 || ($1 == 4 && $2 >= 35)) }' <<< "$version"; then
  echo 'Expected a stable Lean release >= 4.35.0 (for example 4.35.0)' >&2; exit 1
fi
if ! command -v curl >/dev/null || ! command -v jq >/dev/null; then
  echo 'Install curl and jq first' >&2; exit 1
fi
# Fetch only release metadata here. The image pins checksums; workers fetch bytes.
release=$(curl -fsSL --retry 3 --connect-timeout 20 --max-time 60 \
  "https://api.github.com/repos/leanprover/lean4/releases/tags/v$version")
checksum() {
  jq -er --arg name "lean-$version-$1.tar.zst" \
    '.assets[] | select(.name==$name) | .digest |
     select(test("^sha256:[a-f0-9]{64}$")) | ltrimstr("sha256:")' <<< "$release"
}
if ! linux_sha=$(checksum linux) || ! arm_sha=$(checksum linux_aarch64); then
  echo "Official SHA-256 digests are missing for Lean $version" >&2; exit 1
fi
bash "$root/deploy/build.sh" "$app" lean-cloud-build-app:dev
docker build --build-arg APPLICATION_IMAGE=lean-cloud-build-app:dev \
  --build-arg "LEAN_LINUX_SHA256=$linux_sha" --build-arg "LEAN_ARM64_SHA256=$arm_sha" \
  --build-arg "SOURCE_LEAN_VERSION=$version" -t "$image" "$app"
