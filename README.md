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

`||` combines the results of two computations into a pair. `Cloud.exec` records
the results of actions such as `IO` computations. Recorded results are reused
during replay; an external action may run again if interrupted before its result
is recorded.

The current implementation provides direct and replay interpreters over abstract
storage. The direct interpreter is a simple, structurally recursive reference:
it runs parallel children in array order and needs no fuel or scheduling policy.

Replay takes work from an environment-provided [queue](LeanCloud/WorkQueue.lean).
The environment retains pending locations and the final outcome across restarts;
the interpreter executes each selected location without a discovery pass.
Branches may interleave, while results retain their original array order.
Execution currently uses one thread. Distributed workers, on-premises and cloud
adapters, choice, and cancellation are future work.

Build and run the tests with the pinned Lean toolchain:

```sh
lake build
lake test
```

The [test suite](LeanCloudTests/README.md) compares the interpreters and checks
recovery after interruption. The [equivalence proof](LeanCloud/Proofs/WholeRun.lean)
establishes the same result or error and final external state for fresh runs in
the ideal model, with lawful codecs, enough fuel, and a queue that preserves the
direct interpreter's effect order. Arbitrary reordering of stateful effects can
change results; restart correctness and concurrent workers are not covered by
this theorem.

[Queue fairness laws](LeanCloud/Proofs/WorkQueue.lean) separately prove that every
pending location is eventually selected, assuming the environment satisfies the
laws and workers keep polling.
