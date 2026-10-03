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

Run the [complete example](runtime/LeanCloudRuntime/Demo.lean) with three worker
containers, one scheduler, RabbitMQ mailboxes, and shared S3 blob storage:

```sh
docker compose up --build -d --scale worker=3
docker compose logs -f scheduler worker
```

Once the workers finish, read the saved report:

```sh
docker compose run --rm --no-deps worker result /etc/lean-cloud/config.json demo
# files=16, errors=24
```

The [deployment guide](LeanCloud/Deployment.md) explains configuration, submission,
restarts, and integration tests. `docker compose down` stops the stack while
preserving its data.

`||` combines the results of two computations into a pair. Use
`Cloud.pure (fun _ => analyze input)` to record the result of a delayed pure
calculation. Ordinary `pure value` and `return value` retain their usual meaning.
`Cloud.exec` records the results of actions such as `IO` computations. Recorded results are reused
during replay; an external action may run again if interrupted before its result
is recorded.

One scheduler organizes assignments and parallel joins through durable RabbitMQ mailbox
messages. Workers execute the workflow and write immutable replay records directly
to shared blob storage. The scheduler keeps only coordination metadata in its own
local SQLite database. Each actor has its own queue; there is no shared work queue or shared execution database.

The [direct interpreter](LeanCloud/DirectInterpreter.lean) remains the simple
sequential reference. [Sim](LeanCloud/Simulation.md) runs the same scheduler,
workers, and replay interpreter with controlled message delivery, crashes, and
restarts. Parallel results keep their original array order.

```sh
lake build
lake test
```

The [tests](LeanCloudTests/README.md) compare direct and replay execution, including
recovery after scheduler and worker crashes. Real adapter and container checks:

```sh
lake exe cloud_runtime_tests
lake exe cloud_chaos --seed 1
```

The redesign replaces the previous shared-queue protocol and its proofs.
[Current proofs](LeanCloud/Proofs/MainTheorems.lean) cover immutable records,
durable mailbox operations, scheduler recovery, recorded-prefix reconstruction,
and concurrent execution: whenever the scheduler finishes a pure workflow, its
durable result equals direct evaluation, even after crashes and message redelivery.
With sufficient interpreter fuel and recurring opportunities to execute an
assignment and save its report before expiry, the workflow eventually finishes
with that same result. These execution and delivery assumptions are explicit
in the [proof guide](LeanCloud/Proofs/README.md). Choice, cancellation, and
provider-specific deployment automation remain future work.
