#!/usr/bin/env bash
# No network or cloud allocation. Real compression/checksums, mocked transport.
set -euo pipefail
app=$(cd "$(dirname "$0")" && pwd -P)
test_dir=$(mktemp -d)
trap 'rm -rf "$test_dir"' EXIT
mkdir -p "$test_dir/bin" "$test_dir/origin" "$test_dir/data" "$test_dir/deployment"
export WIKI_TEST_DIR="$test_dir"
export PATH="$test_dir/bin:$PATH"
name=enwiki-20261001-pages-articles-multistream
bzip2 -c "$app/fixtures/tiny.xml" > "$test_dir/origin/$name.xml.bz2"
printf '0:1:Proof\n' | bzip2 -c > "$test_dir/origin/$name-index.txt.bz2"
# Keep the manifest order explicit: dump first, index second.
jq --argjson dumpBytes "$(wc -c < "$test_dir/origin/$name.xml.bz2")" \
  --arg dumpSha "$(openssl dgst -sha1 -r "$test_dir/origin/$name.xml.bz2" | cut -d ' ' -f 1)" \
  --argjson indexBytes "$(wc -c < "$test_dir/origin/$name-index.txt.bz2")" \
  --arg indexSha "$(openssl dgst -sha1 -r "$test_dir/origin/$name-index.txt.bz2" | cut -d ' ' -f 1)" \
  '.baseUrl="https://example.invalid/wiki" | .files[0].bytes=$dumpBytes | .files[0].sha1=$dumpSha |
   .files[1].bytes=$indexBytes | .files[1].sha1=$indexSha' "$app/full-wikipedia/snapshot.json" > "$test_dir/snapshot.json"
cat > "$test_dir/bin/curl" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
printf 'download\n' >> "$WIKI_TEST_DIR/downloads"
while [[ $# -gt 1 ]]; do
  if [[ $1 == --output ]]; then output=$2; shift; fi
  shift
done
cp "$WIKI_TEST_DIR/origin/${1##*/}" "$output"
SH
cat > "$test_dir/bin/cloud-app" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
[[ $1 == files && $2 == import && $5 == */index.txt ]]
cmp "$5" <(printf '0:1:Proof\n')
printf 'import\n' >> "$WIKI_TEST_DIR/imports"
printf '{"source":{"test":true}}\n' > "$6"
SH
chmod +x "$test_dir/bin/"*
run() { bash "$app/full-wikipedia/ingest.sh" "$test_dir/snapshot.json" ignored "$test_dir/data"; }
reject() { if "$@" > "$test_dir/rejected.log" 2>&1; then echo 'Expected rejection' >&2; exit 1; fi; }
# A complete .part left by interruption is verified without asking for an EOF range.
cp "$test_dir/origin/$name.xml.bz2" "$test_dir/data/$name.xml.bz2.part"
cp "$test_dir/snapshot.json" "$test_dir/data/snapshot.json"
run > "$test_dir/log"
[[ $(wc -l < "$test_dir/downloads" | tr -d '[:space:]') == 1 ]]
grep -q '^WIKI_PREPARE_REQUEST={"source":' "$test_dir/log"
run > /dev/null
[[ $(wc -l < "$test_dir/downloads" | tr -d '[:space:]') == 1 ]]
printf x | dd of="$test_dir/data/$name.xml.bz2" bs=1 count=1 conv=notrunc 2>/dev/null
reject run
grep -q 'Checksum mismatch' "$test_dir/rejected.log"
[[ $(wc -l < "$test_dir/imports" | tr -d '[:space:]') == 2 ]]
cp "$test_dir/origin/$name.xml.bz2" "$test_dir/data/$name.xml.bz2"
jq '.baseUrl="https://elsewhere.invalid/wiki"' "$test_dir/snapshot.json" > "$test_dir/changed.json"
reject bash "$app/full-wikipedia/ingest.sh" "$test_dir/changed.json" ignored "$test_dir/data"
grep -q 'another snapshot' "$test_dir/rejected.log"
jq '.files[0].name="../escape"' "$test_dir/snapshot.json" > "$test_dir/changed.json"
reject bash "$app/full-wikipedia/ingest.sh" "$test_dir/changed.json" ignored "$test_dir/new-data"
# The rendered job preserves provider identity and is isolated from actor disks.
jq -n '{name:"wiki",context:"fixture",namespace:"wiki",image:("wiki@sha256:"+("a"*64)),
  storageClass:"managed-csi",podLabels:{"azure.workload.identity/use":"true"}}' > "$test_dir/deployment/deployment.json"
bash "$app/full-wikipedia/cluster.sh" render "$test_dir/deployment" "$test_dir/render" > /dev/null
jq -e '.items[]|select(.kind=="Job")|.spec.template.spec as $p |
  .spec.template.metadata.labels["azure.workload.identity/use"]=="true" and
  $p.serviceAccountName=="cloud-node" and $p.restartPolicy=="Never" and
  $p.volumes[0].persistentVolumeClaim.claimName=="wiki-import" and
  $p.containers[0].command[0]=="bash"' "$test_dir/render/ingest.json" >/dev/null
[[ ! -f "$test_dir/render/config.json" ]]
reject bash "$app/full-wikipedia/cluster.sh" render "$test_dir/deployment" "$test_dir/render"
# Completed-job results are read from logs; an unfinished job must not publish one.
owner=$(jq -r '.items[0].metadata.labels["lean-cloud/wiki-ingest"]' "$test_dir/render/ingest.json")
mkdir -p "$test_dir/cluster"
jq -n --arg owner "$owner" '{metadata:{labels:{"lean-cloud/wiki-ingest":$owner}},status:{succeeded:0}}' \
  > "$test_dir/cluster/job_wiki-import.json"
cat > "$test_dir/bin/kubectl" <<'SH'
#!/usr/bin/env bash
set -euo pipefail
while [[ $1 == --* ]]; do
  case "$1" in --context|--namespace|--kubeconfig) shift 2 ;; *) shift ;; esac
done
state="$WIKI_TEST_DIR/cluster"
case "$1" in
  get)
    file="$state/${2//\//_}.json"
    if [[ -f "$file" ]]; then
      if [[ $* == *'-o name'* ]]; then echo "$2"; else cat "$file"; fi
    fi ;;
  logs) printf 'progress\nWIKI_PREPARE_REQUEST={"source":{"test":true}}\n' ;;
  create|apply)
    if [[ $2 == configmap && $3 == wiki-import-operation ]]; then
      mkdir "$state/lock"; exit
    fi
    if [[ $2 == configmap ]]; then
      files=()
      for arg in "$@"; do [[ $arg != --from-file=* ]] || files+=("${arg#--from-file=}"); done
      jq -n --rawfile script "${files[0]}" --rawfile snapshot "${files[1]}" \
        '{kind:"ConfigMap",metadata:{name:"wiki-import"},data:{"ingest.sh":$script,"snapshot.json":$snapshot}}'
      exit
    fi
    payload=$(cat)
    kind=$(jq -r .kind <<< "$payload")
    case "$kind" in Job) resource=job ;; PersistentVolumeClaim) resource=pvc ;; ConfigMap) resource=configmap ;; *) exit 1 ;; esac
    file="$state/${resource}_wiki-import.json"
    [[ $1 != create || ! -f "$file" ]]
    printf '%s\n' "$payload" > "$file"
    echo "$1:$resource" >> "$state/mutations"
    ;;
  delete)
    if [[ $2 == configmap && $3 == wiki-import-operation ]]; then rmdir "$state/lock"; exit; fi
    shift
    for resource in "$@"; do
      [[ $resource != --* ]] || break
      echo "delete:$resource" >> "$state/mutations"
      [[ $resource != job/wiki-import || ! -f "$state/fail-stop" ]] || exit 1
      rm -f "$state/${resource//\//_}.json"
    done
    ;;
  *) echo 'Unexpected kubectl command' >&2; exit 1 ;;
esac
SH
chmod +x "$test_dir/bin/kubectl"
reject bash "$app/full-wikipedia/cluster.sh" result "$test_dir/deployment" "$test_dir/render"
[[ ! -f "$test_dir/render/prepare.json" ]]
jq '.status.succeeded=1' "$test_dir/cluster/job_wiki-import.json" > "$test_dir/job.next"
mv "$test_dir/job.next" "$test_dir/cluster/job_wiki-import.json"
bash "$app/full-wikipedia/cluster.sh" result "$test_dir/deployment" "$test_dir/render" > /dev/null
jq -e .source.test "$test_dir/render/prepare.json" >/dev/null
jq '.metadata.labels["lean-cloud/wiki-ingest"]="another-import"' "$test_dir/cluster/job_wiki-import.json" > "$test_dir/job.next"
mv "$test_dir/job.next" "$test_dir/cluster/job_wiki-import.json"
reject bash "$app/full-wikipedia/cluster.sh" clean "$test_dir/deployment" "$test_dir/render" --yes
grep -q 'Another import owns' "$test_dir/rejected.log"
[[ ! -d "$test_dir/cluster/lock" && ! -f "$test_dir/cluster/mutations" ]]
rm "$test_dir/cluster/job_wiki-import.json"
# A concurrent lifecycle operation must not be able to create or delete resources.
mkdir "$test_dir/cluster/lock"
reject bash "$app/full-wikipedia/cluster.sh" start "$test_dir/deployment" "$test_dir/render"
grep -q 'Import operation is locked' "$test_dir/rejected.log"
[[ -d "$test_dir/cluster/lock" && ! -f "$test_dir/cluster/mutations" ]]
rmdir "$test_dir/cluster/lock"
bash "$app/full-wikipedia/cluster.sh" start "$test_dir/deployment" "$test_dir/render" > /dev/null
[[ -f "$test_dir/cluster/job_wiki-import.json" && -f "$test_dir/cluster/pvc_wiki-import.json" && ! -d "$test_dir/cluster/lock" ]]
# Retrying waits for the old job; failure to stop it cannot launch a replacement.
jq '.status={conditions:[{type:"Failed",status:"True"}]}' "$test_dir/cluster/job_wiki-import.json" > "$test_dir/job.next"
mv "$test_dir/job.next" "$test_dir/cluster/job_wiki-import.json"
printf '\n# Revised ingest script\n' >> "$test_dir/render/ingest.sh"
touch "$test_dir/cluster/fail-stop"
: > "$test_dir/cluster/mutations"
reject bash "$app/full-wikipedia/cluster.sh" retry "$test_dir/deployment" "$test_dir/render"
[[ $(cat "$test_dir/cluster/mutations") == delete:job/wiki-import ]]
[[ -f "$test_dir/cluster/pvc_wiki-import.json" && ! -d "$test_dir/cluster/lock" ]]
rm "$test_dir/cluster/fail-stop"
bash "$app/full-wikipedia/cluster.sh" retry "$test_dir/deployment" "$test_dir/render" > /dev/null
jq -e --rawfile script "$test_dir/render/ingest.sh" '.data["ingest.sh"]==$script' "$test_dir/cluster/configmap_wiki-import.json" >/dev/null
# Cleanup also stops before deleting the disk, and can be repeated.
touch "$test_dir/cluster/fail-stop"
reject bash "$app/full-wikipedia/cluster.sh" clean "$test_dir/deployment" "$test_dir/render" --yes
[[ -f "$test_dir/cluster/pvc_wiki-import.json" && ! -d "$test_dir/cluster/lock" ]]
rm "$test_dir/cluster/fail-stop"
bash "$app/full-wikipedia/cluster.sh" clean "$test_dir/deployment" "$test_dir/render" --yes > /dev/null
bash "$app/full-wikipedia/cluster.sh" clean "$test_dir/deployment" "$test_dir/render" --yes > /dev/null
[[ ! -f "$test_dir/cluster/pvc_wiki-import.json" && ! -f "$test_dir/cluster/job_wiki-import.json" && ! -d "$test_dir/cluster/lock" ]]
printf '{"dataset":{"test":true}}\n' > "$test_dir/prepared.json"
bash "$app/full-wikipedia/requests.sh" "$test_dir/prepared.json" "$test_dir/queries" > /dev/null
jq -e '.dataset.test and (.vocabulary|length==7)' "$test_dir/queries/count.json" >/dev/null
jq -e '.dataset.test and .pattern=="formal verification" and .ignoreCase' "$test_dir/queries/grep.json" >/dev/null
reject bash "$app/full-wikipedia/requests.sh" "$test_dir/prepared.json" "$test_dir/queries"
echo 'PASS full-Wikipedia checksums, resume, lifecycle isolation, retry/cleanup, results and query inputs'
