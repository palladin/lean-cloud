# Cloud reducers

Fused data pipelines distributed across cloud workers, with
[lean-reducers](https://github.com/palladin/lean-reducers) handling multicore
execution inside each worker. This is an optional Lake package; the core cloud
interpreter does not depend on it.

Like the multicore reducer, the cloud reducer splits work into a balanced binary
tree. Each leaf folds a bounded batch locally; each parent combines its two child
results in a recorded worker effect. The root receives one result from each
subtree. Subtrees are delayed, so reconstruction follows only the assigned path.
The scheduler advances each subtree independently: a parent combiner can run
as soon as its own children finish, while other subtrees are still executing.

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
- `sum`, `length`, `reduceMap`: combine aggregates throughout the tree.
- `toArray`: collect bounded outputs such as file references.
- `foldWith`: finalize local accumulators and combine pairs of results on workers.
  For large count tables, save each leaf to blobs, then merge two references into
  a new blob at each parent. Only references enter the journal.

`reduceMap` reuses `MonoidSpec`. The low-level folds also
require a compatible accumulator step: `step x acc = combine (step x unit) acc`.
Associativity and identity laws for the combiner alone do not establish this.
With `foldWith`, merging finalized values must represent finalizing their combined
accumulators. Empty input finalizes the fold's identity once, without reading a
partition. This gives `sum = 0` and `toArray = #[]`.
Partitions and results retain input order, including for noncommutative folds.
Arbitrary IO operations still need their own independence/idempotency contract.

Cloud batches use the **recorded planning environment**, keeping partition
boundaries stable on replay. Local tasks use the **executing attempt's CPU
budget**, including after replacement by a different worker. This is advisory
concurrency, not worker affinity. IO errors are recorded application failures;
node crashes alone trigger replay recovery. Started local tasks are joined
before exceptions escape. Leaf and combiner effects have their own replay
locations, so restart reuses both kinds of recorded result.

`ReducerCloud.Config` controls leaf batch count, maximum items/weight, leaf and
combiner labels, and the local reducer configuration. Blob weights are bytes;
individual ranges default to 8 MiB. The source adapter shares a one-chunk cache and manifest index
among local tasks. Bounded reads can extend by one boundary line, so choose
`maxLineBytes`, batch sizes, and CPU budgets for the worker's memory limit.
Tree depth grows logarithmically with the number of batches. This distributes
combining work but adds forks and recorded effects compared with a flat fan-out;
keep leaves coarse enough to justify cloud scheduling.

The execution topology changed with tree reduction. Version workflows that used
the previous flat reducer before deploying this implementation over existing runs.
`foldWith` replaces `foldPartitions`: supply a pairwise combiner for the finalized
leaf results instead of gathering them all for one final merge.

The [Wiki workflows](../Applications/Wiki/Wiki/Workflow.lean) demonstrate
preparation, vocabulary counting, and grep with results stored in blobs.

From this directory, run `lake test` for generated pipeline comparisons,
replay/environment tests, ordered tree combines, combiner crash recovery, recorded
failures, and authenticated blob seeks.
