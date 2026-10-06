# lean-cloud

[![CI](https://github.com/palladin/lean-cloud/actions/workflows/ci.yml/badge.svg)](https://github.com/palladin/lean-cloud/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.34.1-blue)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green)](LICENSE)

Parallel and distributed programming for Lean.

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
containers, one scheduler container, and shared S3 blob storage. Each node runs its HTTP API, SQLite inbox, and actor in one Lean process:

```sh
docker compose up --build -d scheduler worker worker2 worker3
docker compose exec scheduler cloud-app submit /etc/lean-cloud/config.json example-1
docker compose logs -f scheduler worker worker2 worker3
```

Create your own application from the interactive console:

```sh
lake exe lean_cloud
```

```text
cloud> init my-app
```

Edit `my-app/Main.lean`, then run `deploy` and `run my-app` in the same console.
Use `deploy --workers 4` to choose capacity and `scale N` to resize a running pool.
Use `deployments` and `use NAME` to switch applications, `status` or `doctor` to
inspect them, and `down` / `up` to stop and restart services while preserving data.

The CLI generates the deployment configuration and builds your executable in
Docker. `ps` lists runs; `watch RUN` shows the live branch tree, code, and workers.
Completed, paused, and killed runs show their last view.
Use `pause RUN` / `resume RUN` to stop and continue a run, or `kill RUN` to cancel it permanently.
See the [console guide](LeanCloud/Console.md) for inputs, registration, and recovery.

Once the workers finish, read the saved report:

```sh
docker compose exec scheduler cloud-app result /etc/lean-cloud/config.json example-1
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

One scheduler organizes assignments and parallel joins through durable mailbox
messages. Each worker and the scheduler runs its HTTP API and embedded SQLite inbox in the same Lean process
and persistent mailbox volume. Workers execute the workflow and write immutable replay records directly
to shared blob storage. The scheduler keeps only coordination metadata in its own
local SQLite database. Global blob storage holds replay values and user files.

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

[The main theorems](LeanCloud/Proofs/MainTheorems.lean) prove that sequential
replay from empty storage agrees with direct evaluation of the same pure program.
The concurrent proofs cover immutable records,
durable mailbox operations, scheduler recovery, recorded-prefix reconstruction,
and concurrent execution: whenever the scheduler finishes a pure workflow, its
durable result equals direct evaluation, even after crashes and message redelivery.
With sufficient interpreter fuel and recurring opportunities to execute an
assignment and save its report before expiry, the workflow eventually finishes
with that same result. These execution and delivery assumptions are explicit
in the [proof guide](LeanCloud/Proofs/README.md). Administrative pause/kill commands
are tested separately; the theorems describe workflow evaluation and recovery.
