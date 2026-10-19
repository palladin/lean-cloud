# Full English Wikipedia

Import the full current-articles dump once, prepare article shards in parallel,
then reuse the dataset for word counts and searches. These instructions run the
download **inside your Kubernetes cluster**, close to the blob store. Your laptop
only receives small JSON references; neither the scheduler nor an analysis worker
downloads the entire dump.

The checked-in [snapshot](full-wikipedia/snapshot.json) pins **enwiki 20261001**:

| File | Compressed bytes |
| --- | ---: |
| `enwiki-20261001-pages-articles-multistream.xml.bz2` | 26,917,225,724 |
| `enwiki-20261001-pages-articles-multistream-index.txt.bz2` | 285,227,194 |

The filenames, lengths and SHA-1 checksums were checked against
[Wikimedia's dated download](https://dumps.wikimedia.org/enwiki/20261001/) and
[published checksums](https://dumps.wikimedia.org/enwiki/20261001/enwiki-20261001-sha1sums.txt).
Downloads are verified before import. This is the full current-articles export,
**not revision history**. Preparation selects namespace 0 and excludes redirects;
queries operate on wikitext. Keep the snapshot metadata and follow
[Wikimedia's reuse requirements](https://dumps.wikimedia.org/legal.html).

## 1. Deploy the Wiki application

Use an existing cluster, or create one with the [Azure guide](../../deploy/Azure.md).
Run these commands from the repository root, replacing the deployment paths if
necessary. For Azure ARM64 nodes:

```sh
./Applications/Wiki/build.sh lean-cloud-wiki:dev linux/arm64
./deploy/azure.sh publish .azure-infra lean-cloud-wiki:dev wiki
./deploy/azure.sh configure .azure-infra .wiki-deployment wiki 3
./deploy/kubernetes.sh show .wiki-deployment
```

For an x86 cluster, build with `linux/amd64`. Existing Kubernetes and AWS
deployments use the same import helper once the Wiki image, blob storage and
workload identity are configured by their deployment helpers.

Before `up`, review `deployment.json`. A reasonable starting point is three
workers with `cpuMillis: 1000`, `memoryMiB: 4096`, and
`schedulerResources: {"cpuMillis": 250, "memoryMiB": 512}`. Ensure those requests,
Kubernetes system pods, and the temporary ingest job fit your machines. This is
an initial configuration, not a benchmark or completion-time estimate. Workers
use their configured CPU budget for local reducer tasks.

The ingest job separately requests 0.5 CPU / 1 GiB RAM (limits: 1 CPU / 2 GiB),
and a **64 GiB persistent scratch disk**. Its default time limit is 24 hours;
these settings are editable in the rendered `ingest.json` before starting.
It holds the compressed dump and expanded index, not the expanded XML. Shared
blob storage needs room for the compressed
source, prepared wikitext and query outputs: budget **hundreds of GB**, depending
on the snapshot and results. Preparation also uses bounded temporary space on
worker nodes. This full run is substantially larger than the fixture; runtime
and storage use have not yet been measured on the complete snapshot.

```sh
./deploy/kubernetes.sh up .wiki-deployment
./deploy/kubernetes.sh connect .wiki-deployment 8081
```

Leave that private tunnel running. In a second terminal:

```sh
lake build lean_cloud
lake exe lean_cloud connect wiki-full http://127.0.0.1:8081 \
  --token-file .wiki-deployment/client.token
lake exe lean_cloud programs
```

## 2. Download and import near the blobs

Render ordinary, inspectable Kubernetes resources first:

```sh
./Applications/Wiki/full-wikipedia/cluster.sh render .wiki-deployment .lean-cloud/wiki-full
```

Review `.lean-cloud/wiki-full/ingest.json`, `ingest.sh` and `snapshot.json`.
Nothing has been created yet. The job uses the deployed image and its existing
blob identity. It has no public endpoint and does not submit cloud workflows.
The generated files contain no copied credentials; the job mounts the deployment's
existing configuration secret. One import at a time is allowed per namespace.

```sh
./Applications/Wiki/full-wikipedia/cluster.sh start .wiki-deployment .lean-cloud/wiki-full
./Applications/Wiki/full-wikipedia/cluster.sh logs .wiki-deployment .lean-cloud/wiki-full
```

`start` allocates the ingest disk and starts the download. `logs` follows progress;
Ctrl-C stops following logs, **not the job**. Check it with:

```sh
./Applications/Wiki/full-wikipedia/cluster.sh status .wiki-deployment .lean-cloud/wiki-full
```

The importer verifies both files, expands only the index, and uploads groups of
consecutive compressed streams into immutable blobs. It then publishes a source
manifest. On failure, inspect the logs and use `retry` instead of `start`. Downloads
resume from `.part` files, complete cached files are reverified, and uploads can be
repeated safely. A bad checksum requires removing the indicated corrupt file from
the ingest disk, or cleaning the import and starting again. There is no automatic
retry loop for parsing errors. Completed jobs do not retry.

`retry` first removes the failed job and waits for its pods to stop, then uses
the script and resource settings currently in your import directory. The retained
disk still belongs to the original snapshot; changing snapshots requires a fresh
import. Lifecycle commands are serialized by `wiki-import-operation`. If a command
is forcibly terminated, an administrator must verify it has stopped before
removing that lock ConfigMap. Normal completion and errors release it automatically.

Once the job reports `Complete`, save the request:

```sh
./Applications/Wiki/full-wikipedia/cluster.sh result .wiki-deployment .lean-cloud/wiki-full
```

This writes `.lean-cloud/wiki-full/prepare.json`. Save it before deleting the job;
the request is recovered from the completed job's logs.

## 3. Prepare and watch

```sh
lake exe lean_cloud run wiki-prepare --input .lean-cloud/wiki-full/prepare.json --id enwiki-prepare
lake exe lean_cloud watch enwiki-prepare
```

The cloud reducer distributes compressed groups to workers. They parse and filter
articles, upload NDJSON shards, and return references. The final result contains
the dataset reference, selected article count and shard count.

When completed, press `q`, save the result, and generate query inputs:

```sh
lake exe lean_cloud result enwiki-prepare > .lean-cloud/wiki-full/prepared.json
./Applications/Wiki/full-wikipedia/requests.sh \
  .lean-cloud/wiki-full/prepared.json .lean-cloud/wiki-full/queries
```

## 4. Count and search

The generated count request uses `mathematics`, `theorem`, `proof`, `algorithm`,
`computer`, `science`, and `history`. The grep request finds the literal phrase
`formal verification`, ignoring ASCII case. Edit either JSON file to ask a
different question. Query generation refuses to overwrite existing edits.

```sh
lake exe lean_cloud run wiki-count --input .lean-cloud/wiki-full/queries/count.json --id enwiki-count
lake exe lean_cloud watch enwiki-count
lake exe lean_cloud result enwiki-count

lake exe lean_cloud run wiki-grep --input .lean-cloud/wiki-full/queries/grep.json --id enwiki-grep
lake exe lean_cloud watch enwiki-grep
lake exe lean_cloud result enwiki-grep > .lean-cloud/wiki-full/grep-result.json
```

Run `result` after each workflow completes. Use different run IDs for subsequent
queries. Count results are small summaries; grep returns a blob manifest of result
parts, not all matching text over HTTP. The same dataset can serve both workflows
without repeating preparation. Byte-range reducers read only relevant immutable
chunks and split work across worker CPUs.

## 5. Remove temporary resources

Once `prepare.json` is saved, the ingest disk is unnecessary, even while the
prepare workflow is running:

```sh
./Applications/Wiki/full-wikipedia/cluster.sh clean .wiki-deployment .lean-cloud/wiki-full --yes
```

This deletes only the import job, its configuration map and scratch disk. Imported
blobs, query results and application nodes remain. A successful import need not be
repeated while its blob references remain valid.

For full teardown, follow the deployment guide: remove the application, then
destroy the cluster and storage. Stopping workflows or closing watch does not stop
cloud billing. Keep any results you need before destroying shared storage.

For a local check without any cloud resources, build the image and run
`./Applications/Wiki/test-deployment.sh lean-cloud-wiki:dev`. This exercises the
same ingest script and all three HTTP workflows with a small compressed fixture,
then removes the temporary Docker deployment.

The launch scripts are tested with small compressed fixtures. The full snapshot's
URLs, sizes and checksums have been verified, but the full download and computation
have **not** been run yet. The application's [documented limits](README.md#requests-and-exact-semantics)
still apply; oversized/corrupt inputs fail explicitly rather than being skipped.
