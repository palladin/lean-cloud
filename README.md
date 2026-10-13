# lean-cloud

[![CI](https://github.com/palladin/lean-cloud/actions/workflows/ci.yml/badge.svg)](https://github.com/palladin/lean-cloud/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean-%E2%89%A5%204.35.0-blue)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green)](LICENSE)

Parallel and distributed programming for Lean.

Requires Lean **4.35.0 or later**. This repository pins **4.35.0** in
`lean-toolchain` for reproducible builds; newer releases need compatibility testing.

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

Run the [complete example](runtime/LeanCloudRuntime/Demo.lean) with three workers,
one scheduler and shared blob storage:

```sh
./deploy/build.sh . lean-cloud-demo:dev
./deploy/local.sh init .deployment lean-cloud-demo:dev local 3 8080
./deploy/local.sh up .deployment
lake exe lean_cloud
```

```text
cloud> connect local http://127.0.0.1:8080 --token-file .deployment/client.token
cloud> programs
cloud> run sum-squares --id my-example
cloud> ps
cloud> watch my-example
cloud> result my-example
```

The console uses the same scheduler HTTP API for local and remote deployments.
`watch` shows the branch tree, source and workers; finished runs retain their
last view. Use `pause`, `resume` and `kill` to control a workflow.

Deployment stays outside the console. The optional [shell helpers](deploy/README.md)
provide inspectable Docker, Kubernetes and OpenTofu files. Users can use their
own deployment scripts and existing clusters. See the [console guide](LeanCloud/Console.md).

Applications: [cube-and-conquer SAT solving](Applications/CubeAndConquer/README.md)
and [LeanVerify](Applications/LeanVerify/README.md), which checks GitHub Lean projects by module.

`||` combines the results of two computations into a pair. Use
`Cloud.pure (fun _ => analyze input)` to record the result of a delayed pure
calculation. Ordinary `pure value` and `return value` retain their usual meaning.
`Cloud.exec` records both returned values and uncaught `IO` exceptions. An exception
becomes a `CloudError`; replay reuses that failure without retrying the computation.
Catch exceptions or implement retries inside the supplied `IO` action when needed.
Only crash recovery may repeat an action interrupted before its outcome was recorded.

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
docker compose run --build --rm checks
bash deploy/tests-prepare-app.sh
docker buildx bake -f .github/docker-bake.hcl
lake exe cloud_console_tests --chaos-only
```

[The three main theorems](LeanCloud/Proofs/MainTheorems.lean) prove that sequential,
parallel, and locally restarting parallel replay from empty storage agree with
direct evaluation of the same pure program, given sufficient fuel and correct
codecs. The restart theorem covers any finite worker fault plan. Parallel replay runs children
against a shared read-only journal, unions their disjoint new records, and resumes the parent.
See the [proof guide](LeanCloud/Proofs/README.md). Runtime coordination, scheduler
recovery, deployment availability, and pause/kill are covered by simulation and integration tests.
