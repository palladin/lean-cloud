#!/usr/bin/env bash
set -euo pipefail
[[ $# == 2 ]] || { echo 'Usage: requests.sh PREPARED_RESULT OUTPUT_DIRECTORY' >&2; exit 2; }
jq -e '.dataset|type=="object"' "$1" >/dev/null
mkdir -p "$2"
[[ ! -e "$2/count.json" && ! -e "$2/grep.json" ]] || {
  echo 'Query files already exist; edit them or choose a new output directory.' >&2; exit 1;
}
jq '{dataset,vocabulary:["mathematics","theorem","proof","algorithm","computer","science","history"],ignoreCase:true}' "$1" > "$2/count.json"
jq '{dataset,pattern:"formal verification",regex:false,ignoreCase:true,maxOutputBytes:67108864}' "$1" > "$2/grep.json"
echo "Created $2/count.json and $2/grep.json. Edit the vocabulary or pattern before submitting."
