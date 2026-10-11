#!/usr/bin/env bash
# Create a minimal Lean application; edit/register workflows in Main.lean.
set -euo pipefail
assets=$(cd "$(dirname "$0")" && pwd -P)
source "$assets/common.sh"
[[ $# == 1 || $# == 2 ]] || fail 'Usage: deploy/new-app.sh DIRECTORY [SDK_CHECKOUT]'
directory=$1; name=$(basename "$directory"); identifier "$name"
[[ ! -e "$directory" ]] || fail 'Destination already exists'
mkdir -p "$directory"
sed "s/APP_NAME/$name/g" "$assets/app/Main.lean.in" > "$directory/Main.lean"
sed "s/APP_NAME/$name/g" "$assets/app/lakefile.lean.in" > "$directory/lakefile.lean"
cp "$assets/../lean-toolchain" "$directory/lean-toolchain"
# Generated applications use the same secret/state exclusions as the SDK.
cp "$assets/../.gitignore" "$directory/.gitignore"
cp "$assets/../.dockerignore" "$directory/.dockerignore"
if [[ $# == 2 ]]; then
  need jq
  sdk=$(absolute_dir "$2")
  [[ -f "$sdk/runtime/LeanCloudRuntime/Application.lean" ]] || fail 'Invalid SDK checkout'
  jq -n --arg sdk "$sdk" '{sdk:$sdk}' > "$directory/lean-cloud.local.json"
fi
printf 'Created %s. Register workflows in Main.lean, then build with deploy/build.sh.\n' "$directory"
