#!/usr/bin/env bash
# Thin wrapper over inspectable OpenTofu modules; cloud login remains external.
# plan PROVIDER DIR VARS.json | create|destroy-plan|destroy|outputs DIR
set -euo pipefail
assets=$(cd "$(dirname "$0")" && pwd -P)
source "$assets/common.sh"
need tofu; need jq
# Publish metadata only after the complete output has been read and validated.
# This can also be retried after apply without applying the saved plan again.
save_outputs() {
  tofu -chdir="$directory" output -json cloud > "$directory/cloud.json.pending"
  jq -e 'type=="object"' "$directory/cloud.json.pending" >/dev/null || fail 'Invalid infrastructure outputs'
  mv "$directory/cloud.json.pending" "$directory/cloud.json"
}
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
  # Invalidate both previous plans before changing their inputs. Only publish a
  # complete new plan: init/plan failures must never leave an old one applicable.
  rm -f "$directory/provision.tfplan" "$directory/destroy.tfplan"
  if [[ -f "$directory/terraform.tfvars.json" ]]; then
    # Credentials, disk ownership checks and deployed namespaces must keep
    # referring to the same cluster, including after an unapplied/failed plan.
    if [[ "$provider" == aws ]]; then
      identity_fields='["name","account","region","namespace","worker_zone"]'
    else
      identity_fields='["name","subscription","region","namespace"]'
    fi
    changed=$(jq -r --argjson fields "$identity_fields" --slurpfile saved "$directory/terraform.tfvars.json" \
      '[$fields[] as $key | select(.[$key]!=$saved[0][$key]) | $key] | join(", ")' "$vars")
    [[ -z "$changed" ]] || fail "Cannot change cluster identity ($changed). Use a fresh infrastructure directory."
  fi
  printf '%s\n' "$provider" > "$directory/provider"
  cp "$assets/infrastructure/$provider/main.tf" "$directory/main.tf"
  if [[ ! -f "$directory/.terraform.lock.hcl" ]]; then
    cp "$assets/infrastructure/$provider/.terraform.lock.hcl" "$directory/.terraform.lock.hcl"
  fi
  cp "$vars" "$directory/terraform.tfvars.json"
  tofu -chdir="$directory" init
  tofu -chdir="$directory" plan -out=provision.tfplan.pending
  mv "$directory/provision.tfplan.pending" "$directory/provision.tfplan"
  printf 'Review the plan above. Apply with: deploy/%s.sh create "%s"\n' "$provider" "$directory"
else
  [[ $# == 2 ]] || fail 'Usage: deploy/infrastructure.sh create|destroy-plan|destroy|outputs DIR'
  directory=$(absolute_dir "$2")
  [[ -f "$directory/provider" ]] || fail 'Missing infrastructure state directory'
  case "$command" in
    create) lock_dir "$directory"; tofu -chdir="$directory" apply provision.tfplan; save_outputs ;;
    outputs) lock_dir "$directory"; save_outputs; cat "$directory/cloud.json" ;;
    destroy-plan)
      lock_dir "$directory"
      rm -f "$directory/provision.tfplan" "$directory/destroy.tfplan"
      tofu -chdir="$directory" plan -destroy -out=destroy.tfplan.pending
      mv "$directory/destroy.tfplan.pending" "$directory/destroy.tfplan" ;;
    destroy) lock_dir "$directory"; tofu -chdir="$directory" apply destroy.tfplan ;;
    *) fail 'Unknown infrastructure operation' ;;
  esac
fi
