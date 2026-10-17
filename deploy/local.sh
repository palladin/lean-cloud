#!/usr/bin/env bash
# Usage: local.sh configure DIR IMAGE [NAME [WORKERS [PORT]]]
#        local.sh up|down|status|connect|show DIR
#        local.sh scale DIR WORKERS
#        local.sh clean DIR --yes
set -euo pipefail
assets=$(cd "$(dirname "$0")" && pwd -P)
source "$assets/common.sh"
usage() {
  cat <<'USAGE'
Usage: deploy/local.sh COMMAND ...
  doctor
  configure DIR IMAGE [NAME [WORKERS [PORT]]]  (defaults: lean-cloud, 3, 8080)
  show|up|down|status|connect DIR
  scale DIR WORKERS
  clean DIR --yes

configure writes files only; review them before up. init is an alias for configure.
down retains data. clean permanently removes workflows and locally hosted blobs.
USAGE
}
command=${1:-help}; directory=${2:-}
if [[ "$command" == help || "$command" == --help ]]; then usage; exit; fi
need jq; need docker
if [[ "$command" == doctor ]]; then
  [[ $# == 1 ]] || fail 'Usage: deploy/local.sh doctor'
  need openssl; need shasum
  docker compose version >/dev/null
  docker buildx version >/dev/null
  docker info >/dev/null
  printf 'Docker engine, Compose, Buildx, jq, openssl, and shasum are available.\n'
  exit
fi
[[ "$command" != init ]] || command=configure
case "$command" in
  configure) [[ $# -ge 3 && $# -le 6 ]] || fail 'Usage: local.sh configure DIR IMAGE [NAME [WORKERS [PORT]]]' ;;
  up|down|status|connect|show) [[ $# == 2 ]] || fail "Usage: local.sh $command DIR" ;;
  scale) [[ $# == 3 ]] || fail 'Usage: local.sh scale DIR WORKERS'; number "$3" ;;
  clean) [[ $# == 3 && $3 == --yes ]] || fail 'clean deletes all workflows and locally hosted blobs. Use clean DIR --yes.' ;;
  *) usage; exit 1 ;;
esac
if [[ "$command" == configure ]]; then
  image=$3; name=${4:-lean-cloud}; workers=${5:-3}; port=${6:-8080}
  identifier "$name"; number "$workers"; number "$port"
  (( port < 65536 )) || fail 'Invalid port'
  [[ ! -e "$directory" ]] || fail 'Destination already exists; use a fresh directory.'
  # Resolve once. A mutable tag can never change code underneath existing replay records.
  image=$(docker image inspect "$image" --format '{{.Id}}')
  node_name=$(docker info --format '{{.Name}}')
  need openssl
  mkdir -p "$directory"; directory=$(absolute_dir "$directory"); private_dir "$directory"
  secret > "$directory/client.token"; secret > "$directory/internal.token"
  secret 16 > "$directory/blob-access.token"; secret > "$directory/blob-secret.token"
  jq -n --arg name "$name" --arg image "$image" --arg directory "$directory" \
    --arg nodeName "$node_name" --argjson workers "$workers" --argjson port "$port" \
    '{name:$name,image:$image,directory:$directory,nodeName:$nodeName,workers:$workers,retainedWorkers:$workers,port:$port}' > "$directory/deployment.json"
  jq --rawfile access "$directory/blob-access.token" --rawfile secret "$directory/blob-secret.token" '
    .blobs.accessKey=($access|rtrimstr("\n")) | .blobs.secretKey=($secret|rtrimstr("\n"))
    ' "$assets/config.json" > "$directory/config.json"
  jq --rawfile access "$directory/blob-access.token" --rawfile secret "$directory/blob-secret.token" '
    .identities[0].credentials=[{accessKey:($access|rtrimstr("\n")),secretKey:($secret|rtrimstr("\n"))}]
    ' "$assets/s3.json" > "$directory/s3.json"
  cp "$assets/filer.toml" "$directory/"
else
  directory=$(absolute_dir "$directory")
  private_dir "$directory"
fi
spec="$directory/deployment.json"
[[ -f "$spec" ]] || fail 'Missing deployment.json'
if [[ ( "$command" == up || "$command" == scale ) && -f "$directory/cleanup-started" ]]; then
  fail 'Cleanup has started for this deployment. Finish clean and use a fresh directory to deploy again.'
fi
name=$(jq -er .name "$spec"); identifier "$name"
[[ $(jq -r .directory "$spec") == "$directory" ]] || fail 'Deployment directory has moved; review its bind paths before use.'
compose() { docker compose -p "$name" -f "$directory/compose.json" "$@"; }
mounted_config_permissions() {
  # The host directory stays 0700. Individually mounted files must be readable
  # by both the worker and SeaweedFS UIDs, which differ from the host user.
  chmod 644 "$directory/config.json" "$directory/s3.json" "$directory/filer.toml"
}
render() {
  jq --slurpfile spec "$spec" --rawfile client "$directory/client.token" --rawfile internal "$directory/internal.token" '
    $spec[0] as $s | .client={deployment:$s.name,image:$s.image,token:($client|rtrimstr("\n"))} |
    .scheduler.database="/data/scheduler.sqlite" |
    .mailboxes.scheduler={host:"scheduler-mailbox",port:8080,token:($internal|rtrimstr("\n"))} |
    .mailboxes.workers=[range(1;$s.workers+1) | {worker:"worker\(.)",endpoint:{host:"worker\(.)-mailbox",port:8080,token:($internal|rtrimstr("\n"))}}]
    ' "$directory/config.json" > "$directory/config.next"
  mv "$directory/config.next" "$directory/config.json"
  mounted_config_permissions
  jq -f "$assets/local.compose.jq" "$spec" > "$directory/compose.json"
}
owned_volume() {
  local volume=$1
  local owner
  owner=$(docker volume inspect "$volume" --format '{{index .Labels "lean-cloud.directory"}}')
  [[ "$owner" == "$directory" ]] || fail "Volume $volume belongs to another deployment directory."
}
verify_volumes() {
  [[ ! -f "$directory/volumes.json" ]] && return
  while IFS= read -r volume; do
    docker volume inspect "$volume" >/dev/null || fail "Missing durable volume $volume. Restore it before restarting."
    owned_volume "$volume"
  done < <(jq -r '.[]' "$directory/volumes.json")
}
start() {
  verify_volumes
  # Also repair configurations generated before these mount permissions were set.
  mounted_config_permissions
  # Create every volume before any node starts; persist their names first.
  jq -r --arg name "$name" '.volumes|keys[]|$name+"_"+.' "$directory/compose.json" > "$directory/volumes.next"
  while IFS= read -r volume; do
    # An existing volume must have been reserved by this exact deployment directory.
    if docker volume inspect "$volume" >/dev/null 2>&1; then owned_volume "$volume"
    else docker volume create --label "lean-cloud.directory=$directory" "$volume" >/dev/null; fi
  done < "$directory/volumes.next"
  jq -Rn '[inputs]' < "$directory/volumes.next" > "$directory/volumes.json"
  rm "$directory/volumes.next"
  compose up -d --wait --no-build blobs
  compose up -d --wait --no-build scheduler
  # Boot reconfiguration retains old workers until the stop barrier is confirmed.
  jq -c '.mailboxes.workers' "$directory/config.json" | compose exec -T scheduler cloud-app pool-configure /etc/lean-cloud/config.json >/dev/null
  membership=$(compose exec -T scheduler cloud-app pool-workers /etc/lean-cloud/config.json)
  generation=$(jq -er .generation <<< "$membership")
  desired=$(jq -r .workers "$spec"); retained=$(jq -r .retainedWorkers "$spec")
  for ((i=desired+1; i<=retained; i++)); do
    compose exec -T scheduler cloud-app pool-stopped /etc/lean-cloud/config.json "worker$i" "$generation" >/dev/null
  done
  for ((i=1; i<=desired; i++)); do compose up -d --wait --no-build "worker$i"; done
}
connection() { resolved=$(compose port scheduler 8080); printf 'In cloud CLI: connect %s http://127.0.0.1:%s --token-file "%s/client.token"\n' "$name" "${resolved##*:}" "$directory"; }
case "$command" in
  configure) render; printf 'Created inspectable files in %s. Run: deploy/local.sh up "%s"\n' "$directory" "$directory" ;;
  show) jq . "$spec" ;;
  up) lock_dir "$directory"; start; connection ;;
  down) lock_dir "$directory"; compose stop ;;
  scale)
    lock_dir "$directory"; verify_volumes
    # Stop the entire old generation before replacing config or starting any worker.
    compose stop
    compose down --remove-orphans
    jq --argjson n "$3" '.workers=$n | .retainedWorkers=([.retainedWorkers,$n]|max)' "$spec" > "$spec.next"
    mv "$spec.next" "$spec"; render; start; connection ;;
  status) compose ps ;;
  connect) connection ;;
  clean)
    lock_dir "$directory"
    # A failed cleanup may already have removed some volumes. Check ownership of
    # those remaining, but require complete durable state only when starting.
    if [[ -f "$directory/volumes.json" ]]; then
      while IFS= read -r volume; do
        if docker volume inspect "$volume" >/dev/null 2>&1; then owned_volume "$volume"; fi
      done < <(jq -r '.[]' "$directory/volumes.json")
    fi
    touch "$directory/cleanup-started"
    compose down --remove-orphans --volumes
    if [[ -f "$directory/volumes.json" ]]; then
      while IFS= read -r volume; do
        if docker volume inspect "$volume" >/dev/null 2>&1; then
          owned_volume "$volume"; docker volume rm "$volume" >/dev/null
        fi
      done < <(jq -r '.[]' "$directory/volumes.json")
    fi
    printf 'Deleted deployment %s. Files and credentials retained at %s.\n' "$name" "$directory" ;;
  *) fail 'Unknown local deployment operation' ;;
esac
