#!/usr/bin/env bash
# Thin wrapper over inspectable OpenTofu modules; cloud login remains external.
# plan PROVIDER DIR VARS.json | create|destroy-plan|destroy|outputs DIR
set -euo pipefail
assets=$(cd "$(dirname "$0")" && pwd -P)
source "$assets/common.sh"
need tofu; need jq
command=${1:-}
if [[ "$command" == plan ]]; then
  [[ $# == 4 ]] || fail 'Usage: deploy/infrastructure.sh plan azure|aws DIR VARS.json'
  provider=$2; directory=$3; vars=$4
  [[ "$provider" == azure || "$provider" == aws ]] || fail 'Provider must be azure or aws'
  jq -e 'type=="object"' "$vars" >/dev/null
  mkdir -p "$directory"; directory=$(absolute_dir "$directory")
  private_dir "$directory"
  lock_dir "$directory"
  if [[ -f "$directory/provider" ]]; then
    [[ $(cat "$directory/provider") == "$provider" ]] || fail 'Cannot change provider of existing state'
  fi
  printf '%s\n' "$provider" > "$directory/provider"
  cp "$assets/infrastructure/$provider/main.tf" "$directory/main.tf"
  cp "$vars" "$directory/terraform.tfvars.json"
  tofu -chdir="$directory" init
  tofu -chdir="$directory" plan -out=provision.tfplan
  printf 'Review the plan above. Apply with: deploy/infrastructure.sh create "%s"\n' "$directory"
else
  [[ $# == 2 ]] || fail 'Usage: deploy/infrastructure.sh create|destroy-plan|destroy|outputs DIR'
  directory=$(absolute_dir "$2")
  [[ -f "$directory/provider" ]] || fail 'Missing infrastructure state directory'
  case "$command" in
    create) lock_dir "$directory"; tofu -chdir="$directory" apply provision.tfplan; tofu -chdir="$directory" output -json cloud > "$directory/cloud.json" ;;
    outputs) tofu -chdir="$directory" output -json cloud ;;
    destroy-plan) lock_dir "$directory"; tofu -chdir="$directory" plan -destroy -out=destroy.tfplan ;;
    destroy) lock_dir "$directory"; tofu -chdir="$directory" apply destroy.tfplan ;;
    *) fail 'Unknown infrastructure operation' ;;
  esac
fi
