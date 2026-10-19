#!/usr/bin/env bash
# Runs inside the Wiki image, on the ingest node. No cloud control-plane calls.
set -euo pipefail
[[ $# == 3 ]] || { echo 'Usage: ingest.sh SNAPSHOT CONFIG DIRECTORY' >&2; exit 2; }
snapshot=$1; config=$2; directory=$3
jq -e '
  (.wiki + "-" + .date + "-pages-articles-multistream") as $prefix |
  (.wiki|test("^[a-z0-9]+wiki$")) and (.date|test("^[0-9]{8}$")) and
  (.baseUrl|test("^https://[^ /]+/[^ ]+$")) and
  (.files|length==2) and
  .files[0].name == ($prefix + ".xml.bz2") and
  .files[1].name == ($prefix + "-index.txt.bz2") and
  all(.files[]; (.bytes|type=="number" and .>0 and floor==.) and (.sha1|test("^[a-f0-9]{40}$")))
' "$snapshot" >/dev/null
mkdir -p "$directory"
# A cache belongs to one snapshot. Never resume bytes from a different source.
jq -S . "$snapshot" > "$directory/snapshot.next"
if [[ -f "$directory/snapshot.json" ]]; then
  cmp <(jq -S . "$directory/snapshot.json") "$directory/snapshot.next" || {
    echo 'This directory contains another snapshot. Use a new directory.' >&2; exit 1;
  }
fi
mv "$directory/snapshot.next" "$directory/snapshot.json"
base=$(jq -r .baseUrl "$snapshot")
for i in 0 1; do
  name=$(jq -r ".files[$i].name" "$snapshot")
  bytes=$(jq -r ".files[$i].bytes" "$snapshot")
  digest=$(jq -r ".files[$i].sha1" "$snapshot")
  path="$directory/$name"
  if [[ ! -f "$path" && (! -f "$path.part" || $(wc -c < "$path.part" | tr -d '[:space:]') != "$bytes") ]]; then
    echo "Downloading $name ($bytes bytes); partial downloads resume on retry."
    curl --fail --location --proto '=https' --proto-redir '=https' \
      --connect-timeout 30 --retry 5 --retry-delay 10 --speed-limit 1024 --speed-time 120 \
      --max-filesize "$bytes" --continue-at - --output "$path.part" "$base/$name"
  else
    echo "Verifying cached $name"
  fi
  candidate=$path; [[ -f "$candidate" ]] || candidate="$path.part"
  [[ $(wc -c < "$candidate" | tr -d '[:space:]') == "$bytes" ]] || {
    echo "Incorrect size: $candidate" >&2; exit 1;
  }
  [[ $(openssl dgst -sha1 -r "$candidate" | cut -d ' ' -f 1) == "$digest" ]] || {
    echo "Checksum mismatch: remove $candidate before retrying." >&2; exit 1;
  }
  [[ "$candidate" == "$path" ]] || mv "$candidate" "$path"
done
dump=$(jq -r '.files[0].name' "$snapshot")
index=$(jq -r '.files[1].name' "$snapshot")
echo 'Expanding the verified index (not the XML dump).'
# The full index can exceed the bounded native helper's 1 GiB limit. bzip2
# streams to the dedicated ingest disk; Import.boundaries reads it line by line.
bzip2 -dc "$directory/$index" > "$directory/index.txt.part"
mv "$directory/index.txt.part" "$directory/index.txt"
echo 'Uploading indexed compressed groups to blob storage.'
cloud-app files import "$config" "$directory/$dump" "$directory/index.txt" "$directory/prepare.next"
mv "$directory/prepare.next" "$directory/prepare.json"
echo 'Import complete. Submit the prepare request through the cloud CLI.'
# Completed Kubernetes jobs cannot be exec'd; this small reference is retrievable
# from their logs. No credentials or article contents are printed.
printf 'WIKI_PREPARE_REQUEST=%s\n' "$(jq -c . "$directory/prepare.json")"
