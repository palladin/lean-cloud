# Applications

Applications built on the existing cloud effects and interpreters:

| Application | Distributed work | Status |
| --- | --- | --- |
| [Cube-and-conquer SAT](CubeAndConquer/README.md) | Recursively split with `march_cu`, solve leaves with Kissat | Implemented; blob inputs, checked models, verified proof bundles |
| [LeanBuild](LeanBuild/README.md) | Build a GitHub Lean project using distributed workers and local Lake parallelism | Build artifacts, executables and diagnostics; [Mathlib on AWS walkthrough](LeanBuild/MathlibAWS.md) |
| [Wiki](Wiki/README.md) | Prepare Wikipedia shards, count a vocabulary and search article text | Immutable datasets, exact counts and sharded search results |

See each application's README for its input format, deployment and tests.

## Execution model

The application supplies a compiled registry using the existing
[`CloudProgram`](../LeanCloud/Program.lean) and
[`Application.main`](../runtime/LeanCloudRuntime/Application.lean) interfaces.
Scheduler and workers use the same application image. An application's image
also contains the external tools it runs, such as the SAT solvers and proof
checker, or the Lean toolchain for LeanBuild.

```text
prepare immutable input → submit its manifest → Cloud workflow
                                                │
                                      parallel worker actions
                                                │
                                      artifacts + final report
```

The scheduler assigns branches and coordinates joins. Workers perform planning,
tool execution, artifact transfers and replay-record access, including the
parent continuation after a join.

The C&C workflow recursively splits each subproblem with `march_cu` and dispatches
its children using `Cloud.parallel`. Total decision depth bounds the tree;
`splitDepth` controls how much cubing happens per action. Up to `cubesPerJob`
sibling leaves form one Kissat action followed by a separate proof-checking
action. The [scheduler](../LeanCloud/Scheduler/Program.lean) runs sibling
actions in parallel, and each subtree advances as soon as its own children
finish. Worker count is a deployment setting, independent of the workflow's
depth parameters.

Validate depth and resource limits before starting work. Each tool action uses
an isolated temporary workspace.

## Durable actions

An external action has one replay boundary:

```text
Cloud.exec:
  restore immutable inputs into a temporary workspace
  run a bounded tool process
  validate its output and publish immutable artifacts
  return a small serializable result containing artifact references
```

Do not persist a temporary file path as the result of an effect. A later worker
cannot use it, and replay skips the action that originally created it. Each
action restores its own inputs; local caches are disposable optimizations.

If a worker stops before its result is recorded, the action can run again.
Immutable artifacts make that retry safe; subprocess execution is not exactly
once. Incomplete uploads never become published manifests. Published but
unreferenced artifacts may need later garbage collection.

Expected tool outcomes—solver timeouts and rejected proofs—are
typed application results. They must not become indefinitely retried IO
exceptions. Transport failures remain distinguishable from those outcomes.

## Application support

The runtime provides shared helpers, and each application adds its own input
preparation and test adapters:

| Helper | Contract |
| --- | --- |
| Artifact transfer | [`Files.lean`](../runtime/LeanCloudRuntime/Files.lean) restores/publishes files with SHA-256 verification and returns immutable references |
| Process runner | [`Process.lean`](../runtime/LeanCloudRuntime/Process.lean) streams diagnostics to files, enforces deadlines and monitors file sizes |
| Input preparation | Per application, e.g. SAT's `sat_files prepare` or Wiki's `wiki_files import`, uploads inputs and writes a request containing immutable file references |
| Test adapter | Substitute deterministic tool outcomes; inject failures at transfer, execution and publication boundaries |

The SDK's blob API transfers byte arrays. The runtime's file adapter streams
bounded chunks through that API and publishes immutable file manifests. CNFs,
models, proofs, Wikipedia shards, build artifacts and logs use this path inside
`Cloud.exec`; only file references enter the replay journal.

The runtime checks interruption at replay-store boundaries. It cannot currently
stop an arbitrary long `Cloud.exec` body promptly. Every tool action therefore
needs its own deadline and process cleanup. Prompt pause/kill of subprocess
groups needs a separately tested runtime integration; interpreter fuel is not
a subprocess timeout.

Pin tool versions, source revisions, build options and architecture in the image
and task manifests. Source downloads happen during preparation/image building,
not implicitly during a resumed workflow. Credentials stay in deployment
configuration, outside workflow inputs and reports.

## User experience

Image building, tool downloads, input upload and deployment remain inspectable
external helpers. Users may supply their own scripts and infrastructure.
Deployment commands remain outside the cloud console.

After deploying the application and preparing `input.json`, use the
existing [HTTP console](../LeanCloud/Console.md). For the SAT application's
[local deployment](CubeAndConquer/README.md#run-on-local-workers):

```text
cloud> connect sat http://127.0.0.1:8080 --token-file .sat-deployment/client.token
cloud> programs
cloud> run cube-and-conquer --input input.json --id sat-check
cloud> watch sat-check
cloud> result sat-check
```

The `cube-and-conquer` entry is available in a deployment containing the
application. Reports contain immutable artifact references; use the application's
file helper to download artifacts and independently verify result bundles.

`watch` shows the orchestration code, branch tree and worker metrics. It does not
automatically display a solver's internal search state. Full tool logs are artifacts;
console observations remain short status messages.

## Validation boundary

The [three interpreter theorems](../LeanCloud/Proofs/MainTheorems.lean) concern
pure cloud programs. They do not prove properties of external solvers
or arbitrary IO actions. Test the application's pure planning/aggregation
logic, compare direct and replay execution with deterministic tool adapters,
then run real-tool and crash/recovery integration tests.

Develop the application first against local containers. The same registry and
HTTP client path can then use the existing Kubernetes, Azure or AWS deployment
helpers; no application-specific cloud backend is needed.
