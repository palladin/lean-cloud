#!/bin/sh
# Test fixture only: rendezvous proves actual overlapping tool processes.
set -eu
directory=$(dirname "$0")
kind=$(basename "$0")
width=$(cat "$directory/width")
lock="$directory/lock"
events="$directory/$kind.events"
started="$directory/$kind.started"
mkdir -p "$started"
acquire() { while ! mkdir "$lock" 2>/dev/null; do sleep 0.01; done; }
acquire
printf '1\n' >> "$events"
touch "$started/$$"
rmdir "$lock"
cleanup() {
  acquire
  printf '%s\n' -1 >> "$events"
  rmdir "$lock"
}
trap cleanup EXIT
attempt=0
while [ "$(find "$started" -type f | wc -l)" -lt "$width" ]; do
  attempt=$((attempt + 1))
  [ "$attempt" -lt 200 ] || exit 1
  sleep 0.01
done
case "$kind" in
  kissat)
    # --time=SECONDS FORMULA PROOF
    : > "$3"
    printf 's UNSATISFIABLE\n'
    exit 20 ;;
  drat-trim)
    printf 's VERIFIED\n' ;;
  *) exit 1 ;;
esac
