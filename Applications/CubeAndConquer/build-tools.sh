#!/usr/bin/env bash
# Downloads/builds only inside DESTINATION. No system installation or sudo.
# shellcheck source-path=SCRIPTDIR
set -euo pipefail
app=$(cd "$(dirname "$0")" && pwd -P)
source "$app/tools.lock"
[[ $# -le 1 ]] || { echo 'Usage: build-tools.sh [DESTINATION]' >&2; exit 1; }
destination=${1:-"$app/../../.lean-cloud/sat-tools"}
jobs=${JOBS:-2}
[[ "$jobs" =~ ^[1-9][0-9]*$ ]] || { echo 'JOBS must be positive' >&2; exit 1; }
for tool in curl tar make cc; do command -v "$tool" >/dev/null; done
digest() {
  if command -v sha256sum >/dev/null; then sha256sum "$1" | cut -d ' ' -f 1
  else shasum -a 256 "$1" | cut -d ' ' -f 1; fi
}
mkdir -p "$destination"
destination=$(cd "$destination" && pwd -P)
# A failed build leaves no success stamp and is safe to retry.
mkdir "$destination/.building" 2>/dev/null || { echo "Another build owns $destination/.building" >&2; exit 1; }
trap 'rmdir "$destination/.building"' EXIT
mkdir -p "$destination/downloads" "$destination/src" "$destination/bin"
fetch() {
  local name=$1 repo=$2 revision=$3 checksum=$4
  local archive="$destination/downloads/$name.tar.gz"
  if [[ ! -f "$archive" ]]; then
    curl -fL --retry 3 --connect-timeout 20 --max-time 180 \
      "https://codeload.github.com/$repo/tar.gz/$revision" -o "$archive.partial"
    [[ $(digest "$archive.partial") == "$checksum" ]] || { echo "$name: checksum mismatch" >&2; exit 1; }
    mv "$archive.partial" "$archive"
  fi
  [[ $(digest "$archive") == "$checksum" ]] || { echo "$name: cached checksum mismatch" >&2; exit 1; }
  # Always unpack clean source. Build outputs never replace the reviewed archive.
  local source_dir="$destination/src/$name-$revision"
  if [[ -d "$source_dir" ]]; then rm -rf "$source_dir"; fi
  mkdir -p "$source_dir"
  tar -xzf "$archive" --strip-components=1 -C "$source_dir"
}
fetch kissat arminbiere/kissat "$KISSAT_REV" "$KISSAT_SHA256"
fetch march marijnheule/CnC "$MARCH_REV" "$MARCH_SHA256"
fetch drat marijnheule/drat-trim "$DRAT_REV" "$DRAT_SHA256"
(
  cd "$destination/src/kissat-$KISSAT_REV"
  ./configure --safe --no-embedded
  make -j "$jobs"
)
# march's historical headers use tentative globals; modern GCC defaults to
# -fno-common. Preserve the upstream program's intended common-symbol linkage.
make -C "$destination/src/march-$MARCH_REV/march_cu" -j "$jobs" CC=cc \
  CFLAGS='-O3 -fno-strict-aliasing -fcommon -Wall -DNDEBUG'
cp "$destination/src/kissat-$KISSAT_REV/build/kissat" "$destination/bin/"
cp "$destination/src/march-$MARCH_REV/march_cu/march_cu" "$destination/bin/"
make -C "$destination/src/drat-$DRAT_REV" drat-trim
cp "$destination/src/drat-$DRAT_REV/drat-trim" "$destination/bin/"
cp "$app/tools.lock" "$destination/tools.lock"
printf '%s kissat\n%s march_cu\n%s drat-trim\n' "$(digest "$destination/bin/kissat")" \
  "$(digest "$destination/bin/march_cu")" "$(digest "$destination/bin/drat-trim")" > "$destination/bin.sha256"
# Keep complete corresponding sources and their notices alongside the binaries.
printf 'Built Kissat %s and march_cu %s\nBinaries: %s/bin\nSources and notices: %s/src\n' \
  "$KISSAT_REV" "$MARCH_REV" "$destination" "$destination"
