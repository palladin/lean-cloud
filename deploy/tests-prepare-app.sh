#!/usr/bin/env bash
# Test fixture only. Builds the same registered application users would deploy.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd -P)
app="$root/.lean-cloud/ci-chaos/application"
if [[ ! -d "$app" ]]; then "$root/deploy/new-app.sh" "$app" "$root"; fi
mkdir -p "$app/ChaosFixture"
printf '\nlean_lib ChaosFixture\n' > "$app/library.fragment"
# Recreate metadata so preparation is idempotent.
cp "$root/lean-toolchain" "$app/lean-toolchain"
sed 's/APP_NAME/chaos-fixture/g' "$root/deploy/app/lakefile.lean.in" > "$app/lakefile.lean"
cat "$app/library.fragment" >> "$app/lakefile.lean"
cp "$root/LeanCloudTests/GeneratedProgram.lean" "$app/ChaosFixture/"
sed 's/import LeanCloudTests.GeneratedProgram/import ChaosFixture.GeneratedProgram/' \
  "$root/LeanCloudTests/PoolWorkload.lean" > "$app/ChaosFixture/PoolWorkload.lean"
cp "$root/LeanCloudTests/StressWorkload.lean" "$app/ChaosFixture/"
cp "$root/LeanCloudTests/Fixtures/PoolChaosMain.lean.in" "$app/Main.lean"
