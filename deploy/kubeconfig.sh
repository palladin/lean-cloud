#!/usr/bin/env bash
# Provider CLIs consume the user's existing login. This helper never signs in.
set -euo pipefail
assets=$(cd "$(dirname "$0")" && pwd -P)
source "$assets/common.sh"
need jq
[[ $# == 1 ]] || fail 'Usage: deploy/kubeconfig.sh INFRASTRUCTURE_DIR'
directory=$(absolute_dir "$1"); vars="$directory/terraform.tfvars.json"; cloud="$directory/cloud.json"
private_dir "$directory"
provider=$(jq -er .provider "$cloud"); name=$(jq -er .name "$cloud")
case "$provider" in
  azure)
    need az; need kubelogin
    az aks get-credentials --subscription "$(jq -er .subscription "$vars")" \
      --resource-group "$(jq -er .resourceGroup "$cloud")" --name "$name" --file "$directory/kubeconfig" --overwrite-existing
    kubelogin convert-kubeconfig --kubeconfig "$directory/kubeconfig" -l azurecli ;;
  aws)
    need aws
    aws eks update-kubeconfig --profile "$(jq -er .profile "$vars")" --region "$(jq -er .region "$cloud")" \
      --name "$name" --kubeconfig "$directory/kubeconfig" --alias "$name" ;;
  *) fail 'Unsupported provider' ;;
esac
printf 'export KUBECONFIG="%s/kubeconfig"\n' "$directory"
