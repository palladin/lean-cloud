# Cloud reducers

Fused data pipelines distributed across cloud workers, with
[lean-reducers](https://github.com/palladin/lean-reducers) handling multicore
execution inside each worker. This is an optional Lake package; the core cloud
interpreter does not depend on it.

```lean
import LeanCloudReducers

open LeanCloud LeanCloudRuntime LeanReducers

def countWords (store : IO ObjectStore) (files : Array FileRef) : Cloud IO Nat := cloud {
  let words := (ReducerCloud.readLines store files)
    |>.flatMap (fun line => ReducerSeq.ofList (line.splitOn " "))
    |>.filter (fun word => !word.isEmpty)
  words.length
}
```

`readLines` splits even a single large file into byte ranges. Workers fetch only
the intersecting immutable chunks. The same lean-reducers code used for local
file seeks repairs newline boundaries, so ranges can cut through lines or UTF-8
characters without losing or duplicating a line. Empty files and trailing
newlines follow `String.splitOn "\n"`; pass `trailingEmpty := false` for NDJSON.

The provider adapter verifies the manifest and each fetched chunk's SHA-256;
partial reads do not recompute the whole-file SHA-256. That additional check is
performed by `Files.download`. Raw compressed files cannot be split at arbitrary
byte positions: Wiki first splits bzip2 streams and prepares NDJSON artifacts.

The main combinators are:

- `ofArray`, `ofArrayIO`: pure inputs or independent IO operations.
- `ofPartitions`: adapt another `ReducerParM` producer.
- `readLines`, `readLinesWithFile`: blob-backed seekable sources.
- `map`, `filter`, `flatMap`, `tryMap`: fused transformations and checked parsing.
- `sum`, `length`, `reduceMap`: aggregate results.
- `toArray`: collect bounded outputs such as file references.
- `foldPartitions`: finalize each local aggregate before recording it, for
  example by saving a large count table in blobs and returning its `FileRef`.

`reduceMap` reuses `MonoidSpec`. The low-level `fold` and `foldPartitions` also
require a compatible accumulator step: `step x acc = combine (step x unit) acc`.
Associativity and identity laws for the combiner alone do not establish this.
Partitions and results retain input order, including for noncommutative folds.
Arbitrary IO operations still need their own independence/idempotency contract.

Cloud batches use the **recorded planning environment**, keeping partition
boundaries stable on replay. Local tasks use the **executing attempt's CPU
budget**, including after replacement by a different worker. This is advisory
concurrency, not worker affinity. IO errors are recorded application failures;
node crashes alone trigger replay recovery. Started local tasks are joined
before exceptions escape.

`ReducerCloud.Config` controls batch count, maximum items/weight, labels, and
the local reducer configuration. Blob weights are bytes; individual ranges
default to 8 MiB. The source adapter shares a one-chunk cache and manifest index
among local tasks. Bounded reads can extend by one boundary line, so choose
`maxLineBytes`, batch sizes, and CPU budgets for the worker's memory limit.

The [Wiki workflows](../Applications/Wiki/Wiki/Workflow.lean) demonstrate
preparation, vocabulary counting, and grep with results stored in blobs.

From this directory, run `lake test` for generated pipeline comparisons,
replay/environment tests, recorded failures, and authenticated blob seeks.
