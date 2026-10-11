#!/usr/bin/env bash
# Check actual Docker filtering with dummy secrets, without building a runtime.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd -P)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
context="$work/context"
mkdir -p "$context/deploy"
cp "$root/.dockerignore" "$context/.dockerignore"
printf 'FROM scratch\nCOPY . /\n' > "$context/Dockerfile"
printf 'public source\n' > "$context/Main.lean"
printf '{}\n' > "$context/deploy/config.json"
printf '{}\n' > "$context/deploy/s3.json"
printf '# Public helper source\n' > "$context/deploy/kubeconfig.sh"
for path in config.json custom-state/config.json custom-state/config.next custom-state/storage.json custom-state/s3.json \
    custom-state/client.token custom-state/kubeconfig custom-state/kubeconfig.yaml custom-state/cloud.json \
    custom-state/deployment.json custom-state/resources.json custom-state/compose.json \
    custom-state/terraform.tfstate custom-state/provision.tfplan custom-state/private.tfvars \
    custom-state/private.tfvars.json custom-state/.terraform/credentials.json \
    nested/.deployment/private.txt nested/.azure/accessTokens.json nested/.aws/credentials \
    nested/.kube/config .env .env.private .aws/credentials .azure/accessTokens.json \
    .kube/config lean-cloud.local.json; do
  mkdir -p "$(dirname "$context/$path")"
  printf 'PRIVATE_BUILD_CONTEXT_SENTINEL\n' > "$context/$path"
done
docker buildx build --network=none --output "type=local,dest=$work/export" "$context" >/dev/null
if grep -r -q PRIVATE_BUILD_CONTEXT_SENTINEL "$work/export"; then
  echo 'Private data entered the Docker build context' >&2
  exit 1
fi
for path in Main.lean deploy/config.json deploy/s3.json deploy/kubeconfig.sh; do
  [[ -f "$work/export/$path" ]] || { echo "Missing public source: $path"; exit 1; }
done
printf 'Docker build context excludes private state and keeps public fixtures.\n'
