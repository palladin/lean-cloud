**lean-cloud** brings parallel and distributed programming to Lean.

Use simple monadic code to split work into smaller computations, run them in
parallel, and combine their results.

The following workflow counts error lines across log files in shared blob storage
and saves a combined report. It assumes a `splitIntoBatches` helper:

```lean
import LeanCloud

open LeanCloud

def summarizeLogs (files : Array String) (batchSize : Nat := 100) : Cloud IO BlobRef := cloud {
  let batches := splitIntoBatches files batchSize

  -- Count error lines in each batch.
  let counts ← Cloud.parallel (batches.map fun batch => cloud {
    let mut errors := 0
    for name in batch do
      let text ← CloudBlob.readTextByName name
      errors := errors + ((text.splitOn "\n").filter fun line => line.startsWith "ERROR").length
    return errors
  })

  -- Combine the counts and save the report.
  let total := counts.foldl (· + ·) 0
  CloudBlob.putText s!"files={files.size}, errors={total}"
}

def dailyReport : Cloud IO BlobRef :=
  summarizeLogs #["logs/api-01.txt", "logs/api-02.txt", "logs/worker-01.txt"] 2
```

The three files are split into two batches: one contains the first two files and
the other contains the third. `Cloud.parallel` returns one count per batch. The
workflow sums the counts, saves the report, and returns its `BlobRef`.

`||` combines the results of two computations into a pair. Use
`Cloud.pure (fun _ => analyze input)` to record the result of a delayed pure
calculation. Ordinary `pure value` and `return value` retain their usual meaning.
`Cloud.exec` records the results of actions such as `IO` computations. Recorded results are reused
during replay; an external action may run again if interrupted before its result
is recorded.

The interpreters use separate interfaces: [Db](LeanCloud/Db.lean) stores execution
records; [BlobStorage](LeanCloud/BlobStorage.lean) handles user blobs. The direct interpreter is a simple, structurally recursive reference:
it runs parallel children in array order and needs no fuel or scheduling policy.

Replay takes work from an environment-provided [queue](LeanCloud/WorkQueue.lean).
The environment retains pending locations and the final outcome across restarts;
the interpreter executes each selected location without a discovery pass.
Branches may interleave, while results retain their original array order.
Execution currently uses one thread. Distributed workers, on-premises and cloud
adapters, choice, and cancellation are future work.

[JournalDb](LeanCloud/JournalDb.lean) stores each child's outcome separately, so
sibling completions cannot overwrite each other. The
[lease adapter](LeanCloud/LeaseQueue.lean) publishes successors or the final result
before acknowledging a delivery.

The [worker simulation](LeanCloud/Simulation.md) runs the same interpreter over
`SimM`. An external driver interleaves atomic backend operations, delays replies,
crashes workers, restarts them with fresh local state, and advances lease time.
Durable records and queued work survive. Single-worker recovery and concurrent
execution use this same model.

Build and run the tests with the pinned Lean toolchain:

```sh
lake build
lake test
```

The [test suite](LeanCloudTests/README.md) compares the interpreters and checks
recovery after interruption. The [equivalence proof](LeanCloud/Proofs/QueueContract.lean)
shows that pure workflows return the same value or error under direct evaluation
and replay with a lawful, fair queue and sufficient fuel. Branches may be selected
in any order.

The [proof model](LeanCloud/Proofs/README.md) covers ordinary pure values, delay,
failure, and parallel control flow. The main
[`ConcurrentRecovery.same_output`](LeanCloud/Proofs/ConcurrentEquivalence.lean)
theorem proves that concurrent replay returns the direct interpreter's outcome
and stores its encoding in the durable completion record. Fair scheduling and
delivery after crashes stop supply a completing prefix and sufficient finite fuel.
Runtime exec and blob operations remain available outside this theorem; real
storage and cloud adapters still need implementation and validation.
