# Wiki

Ask concrete questions of a large Wikipedia dump using ordinary cloud programs:
count a vocabulary, or find articles containing a phrase or regular expression.
Prepare the dataset once; reuse its immutable blob reference for many queries.

| Program | Result |
| --- | --- |
| `wiki-prepare/v1` | Article shards and a reusable dataset reference |
| `wiki-count/v1` | Occurrences and matching-article counts for each vocabulary word |
| `wiki-grep/v1` | Matching articles, first-match positions and excerpts in blob files |

```lean
cloud {
  let parts ← Cloud.parallel (dataset.shards.map fun shard => cloud {
    Cloud.exec (fun _ => backend.count request shard) "count vocabulary"
  })
  Cloud.exec (fun _ => backend.sumCounts request parts) "combine counts"
}
```

The real workflows are in [Workflow.lean](Wiki/Workflow.lean). Workers read and
write blobs; the scheduler coordinates branches. Only summaries and immutable
file references enter the replay journal. Each partial count table is stored in
blobs; aggregation reads one table at a time, so it does not retain every
worker's vocabulary table in memory.

## First example, locally

Run from the **lean-cloud repository root**. Docker must be running; the host
needs Lean, Docker and `jq`. The image contains the native libraries.

```sh
lake build lean_cloud
./Applications/Wiki/build.sh
./deploy/local.sh configure .wiki-deployment lean-cloud-wiki:dev wiki-demo 3 8080
./deploy/local.sh up .wiki-deployment

./Applications/Wiki/local-files.sh .wiki-deployment import-xml \
  Applications/Wiki/fixtures/tiny.xml /tmp/wiki-prepare.json

lake exe lean_cloud connect wiki-demo http://127.0.0.1:8080 \
  --token-file .wiki-deployment/client.token
lake exe lean_cloud programs
lake exe lean_cloud run wiki-prepare --input /tmp/wiki-prepare.json --id prepare-wiki
lake exe lean_cloud watch prepare-wiki
```

When preparation completes, press `q` to leave watch and retrieve its result:

```sh
lake exe lean_cloud result prepare-wiki > /tmp/wiki-prepared.json
jq '{dataset, vocabulary:["proof","theorem","algorithm","computer"]}' \
  /tmp/wiki-prepared.json > /tmp/wiki-count.json
lake exe lean_cloud run wiki-count --input /tmp/wiki-count.json --id vocabulary
lake exe lean_cloud watch vocabulary
lake exe lean_cloud result vocabulary
```

The fixture has three selected articles. Expected counts are `proof: 4`,
`theorem: 1`, `algorithm: 2`, `computer: 1`. `proof` occurs in two articles.

Search the same dataset:

```sh
jq '{dataset, pattern:"π proof"}' /tmp/wiki-prepared.json > /tmp/wiki-grep.json
lake exe lean_cloud run wiki-grep --input /tmp/wiki-grep.json --id search
lake exe lean_cloud watch search
lake exe lean_cloud result search > /tmp/wiki-search.json
jq .results /tmp/wiki-search.json > /tmp/wiki-result-ref.json
./Applications/Wiki/local-files.sh .wiki-deployment download \
  /tmp/wiki-result-ref.json /tmp/wiki-matches.json
jq '.parts[0].file' /tmp/wiki-matches.json > /tmp/wiki-part-ref.json
./Applications/Wiki/local-files.sh .wiki-deployment download \
  /tmp/wiki-part-ref.json /tmp/wiki-hits.jsonl
cat /tmp/wiki-hits.jsonl
```

For a large result, download each entry in `parts`. The parts retain dataset
order; articles retain their original dump order. There is one hit per matching
article, reporting its first match. The fixture match belongs to `Computers`.

Remove the temporary deployment and its data when finished:

```sh
./deploy/local.sh clean .wiki-deployment --yes
```

## A large dump

Download a **dated** `pages-articles-multistream.xml.bz2` and its matching
`pages-articles-multistream-index.txt.bz2` from
[Wikimedia dumps](https://dumps.wikimedia.org/backup-index.html). Verify them
against that snapshot's published checksums before importing. Do not mix dates
or use a history dump. Keep the source URL, date and license information with
any dataset you redistribute.

```sh
./Applications/Wiki/local-files.sh .wiki-deployment import \
  /path/to/wiki-pages-articles-multistream.xml.bz2 \
  /path/to/wiki-pages-articles-multistream-index.txt.bz2 \
  /tmp/wiki-prepare.json
```

Then submit `wiki-prepare` as above. The helper streams the compressed source
into immutable blobs, grouped at indexed bzip2 stream boundaries. Preparation
parses these groups in parallel and writes article shards. It does not first
expand the entire dump on one machine. No worker fetches the entire dump.

The Compose helper temporarily copies the source into the scheduler container
for upload, so it needs enough temporary disk space. For larger installations,
run the application's `wiki_files import CONFIG DUMP INDEX OUTPUT` executable
on an ingest machine with a runtime configuration that can reach the blob store.
This is a file utility; the cloud console remains an HTTP workflow client.

The same application image can use the existing [Azure deployment helpers](../../deploy/Azure.md)
and HTTP client. In that guide's publishing step, replace the demo's
`docker buildx build` command with:

```sh
./Applications/Wiki/build.sh "$cloud_repository:demo" linux/arm64
```

Use `linux/amd64` for an x86 cluster. This helper includes Wiki's XML and bzip2
libraries. Continue with the guide's push, digest and deployment steps.
Deployment and provisioning remain outside Wiki workflows.

## Requests and exact semantics

Every request uses immutable `FileRef` objects, as produced by the helpers.
Optional fields have defaults:

- Prepare: `source`, `shardBytes` (32 MiB), `namespaceId` (0),
  `includeRedirects` (false).
- Count: `dataset`, `vocabulary`, `ignoreCase` (true).
- Grep: `dataset`, `pattern`, `regex` (false), `ignoreCase` (false),
  `maxOutputBytes` (64 MiB **per input shard**).

Text is **wikitext**, with XML entities decoded. Templates, links and references
remain in it; counts are not counts of rendered prose. Title/revision metadata
is retained, but searching/counting applies only to article text.

Counting uses maximal `[A-Za-z]+` words and optional ASCII case folding.
Vocabulary entries must be unique after folding, with at most 10,000 entries
of 100 letters each. This initial tokenizer targets English; it is not a
multilingual segmentation algorithm. Grep accepts UTF-8 literals. Regex uses
POSIX extended expressions in the C locale (byte semantics, not Unicode
character classes); back references are unsupported. Case folding is ASCII.
Offsets and match lengths are **zero-based UTF-8 byte counts** in decoded text.
Excerpts are bounded and do not imply that the full match fits in the excerpt.

Prepared shards are NDJSON: one article record per line. Import targets 16 MiB
compressed groups; preparation targets 32 MiB output shards without splitting
articles. A large article can exceed the target size. Hard limits are 256 MiB
compressed per group, 1 GiB expanded per group or compressed index, 8 MiB per
text field, 64 MiB per encoded article, 128 MiB
per output shard, and 10,000 parts/shards per manifest. XML processing and shard
scans have five-minute budgets; OS/container limits remain the hard boundary
for a native regex call. Inputs exceeding a limit fail explicitly. Grep never
silently truncates results. Full history dumps, suppressed text and non-wikitext
selected pages are rejected. DTDs and custom entity declarations are rejected.

Artifacts are content-addressed. A restarted worker can repeat an unfinished
analysis, but recorded results are reused. Ordinary parsing/IO exceptions are
recorded workflow failures, not node crashes to retry indefinitely.

## Development and tests

On macOS install Xcode Command Line Tools. On Ubuntu install `libexpat1-dev`,
`libbz2-dev`, `bzip2`, `openssl` and the normal runtime build prerequisites.

```sh
cd Applications/Wiki
lake build cloud_app wiki_files wiki_tests
lake test
```

From the repository root, `./Applications/Wiki/test-deployment.sh IMAGE` also
tests three shards through real HTTP scheduler/worker containers, then removes
the temporary deployment.

Tests cover generated corpora, shard-boundary invariance, real XML/bzip2 parsing,
entities/CDATA, namespace/redirect filtering, literal/regex matching, corrupt
inputs, output limits, concurrent replay and restart. `wiki_tests --dump FILE`
also prepares and counts a bounded complete XML/bzip2 file. No external downloads
or cloud resources are required by the default test suite.

Stats, extraction, rendered-prose conversion and indexed search are future
programs; the first release contains preparation, count and grep.
