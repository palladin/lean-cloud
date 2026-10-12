# Distributed cube-and-conquer SAT

Upload a DIMACS CNF file, split and solve it on lean-cloud workers, and retrieve a
checked SAT model or a verified UNSAT proof bundle. The application uses
**march_cu**, **Kissat**, and the separate **drat-trim** certificate checker.

The [workflow](CubeAndConquer/Workflow.lean) uses ordinary `Cloud.exec` and
`Cloud.parallel`. No application-specific interpreter or cloud primitives are needed.

## Run on local workers

From the repository root:

```sh
bash deploy/build.sh Applications/CubeAndConquer lean-cloud-sat-app:dev
docker buildx build --load --build-arg APPLICATION_IMAGE=lean-cloud-sat-app:dev \
  -t lean-cloud-sat:dev Applications/CubeAndConquer
bash deploy/local.sh init .sat-deployment lean-cloud-sat:dev sat 3 8080
bash deploy/local.sh up .sat-deployment

# Upload the actual CNF to this deployment's blob store.
bash Applications/CubeAndConquer/local-files.sh .sat-deployment prepare \
  Applications/CubeAndConquer/examples/pigeonhole.cnf > input.json
lake exe lean_cloud
```

```text
cloud> connect sat http://127.0.0.1:8080 --token-file .sat-deployment/client.token
cloud> run cube-and-conquer --input input.json --id pigeons
cloud> ps
cloud> watch pigeons
cloud> result pigeons
```

After completion, save the result and recheck its evidence:

```sh
lake exe lean_cloud result pigeons > report.json
bash Applications/CubeAndConquer/local-files.sh .sat-deployment verify report.json
jq '.bundle' report.json > bundle-ref.json
bash Applications/CubeAndConquer/local-files.sh .sat-deployment download bundle-ref.json > bundle.json

# For SAT (use examples/sat.cnf instead of pigeonhole.cnf):
jq '.outcome.sat.model' report.json > model-ref.json
bash Applications/CubeAndConquer/local-files.sh .sat-deployment download model-ref.json > model.sat
```

The helper uses the **existing** scheduler container's private network and blob
configuration for file transfers. It does not submit work there or create new
containers. Solving and initial certificate checking run on workers. The explicit
`verify` command runs a fresh check wherever the file utility is invoked.

Stop: `bash deploy/local.sh down .sat-deployment`.
Delete the test deployment and its blobs: `bash deploy/local.sh clean .sat-deployment --yes`.

## Input and result contract

`input.json` contains **a CNF file reference**, not CNF text, paths, credentials,
or executable names. Edit its parameters before submission:

| Parameter | Default | Meaning |
| --- | --- | --- |
| `depth` | 10 | Total decision-depth budget; 0 goes directly to Kissat |
| `maxCubes` | 4096 | Leaf safeguard, 1–100000; must accommodate `2^depth` |
| `splitDepth` | 2 | Decision levels per `march` invocation, 1–8 |
| `seconds` | 300 | Cuber/solver time budget per invocation, 1–86400 |
| `verifySeconds` | 600 | Per-cube checker time budget, 1–86400 |

For example, `depth = 4` and `splitDepth = 2` first generate up to four cubes.
Each cube gets a cloud branch which can split into up to four more leaves. Each
leaf runs Kissat, then a separately recorded certificate check. The tree contains
at most 16 leaves, and may be smaller if cubing finishes early. `depth = 0`
creates one solver task without invoking march. Zero is never passed as march's
`-d` argument (which would select its dynamic cutoff).

Each split consumes the actual number of new decision literals. The workflow
checks complete coverage, fresh variables, and the per-call depth before creating
children. A split that makes no progress becomes a solver leaf. `maxCubes` is a
conservative preflight bound: for example, depth 13 requires at least 8192. A
request exceeding the bound is rejected before any tools run.

The workflow uses nested `Cloud.parallel`, with no wave-size setting. Sibling
cubing actions run across available workers; the current scheduler processes
nested subtrees batch by batch. Worker count is a deployment setting. Repeated
march calls reload and preprocess the restricted CNF, so `splitDepth` controls
the tradeoff between task granularity and parallelism.

SAT returns a model file in standard `s`/`v` DIMACS output format, checked against
every original clause and the winning cube's assumptions. All parallel branches
finish; finding SAT does not cancel siblings or skip remaining subtrees.

UNSAT requires a complete binary cube cover and a successfully checked proof for
**every** cube. The bundle contains the input reference, complete cube plan,
per-cube assumptions, the exact CNF including cube units, binary DRAT
proof, verification log, solver logs, tool revisions, and executable digests.
`verify` downloads this evidence, reconstructs every cube formula, checks its
hash against the stored formula, and reruns the checker. Duplicate/missing cubes,
wrong formulas, invalid models and invalid proofs cannot establish UNSAT.

Timeouts or failed certificate checks are **inconclusive**, never UNSAT. The
bundle retains each task's outcome so unresolved cubes can be identified.
Storage/transport failures use normal worker retry behavior. Certificates are
checked by the pinned external checker, **not a theorem proved in Lean**.

Files are immutable, SHA-256-addressed **4 MiB blob chunks plus a manifest**.
A `FileRef` contains that manifest's `BlobRef`, total size and file SHA-256.
Chunks and the entire file are checked on download. Only complete manifests are
published; retries reuse chunks. Solver workspaces, CNF contents and proof bytes
never enter replay records. A published result is reusable after worker restart.
Unreferenced files left by interrupted attempts currently require operator-managed
retention/garbage collection; the application never deletes shared input blobs.

## Other deployments and native use

The application uses the runtime's existing S3/Azure blob adapters and credentials.
It introduces no scheduler API for file bytes. For Kubernetes/cloud use, run the
file utility with a reachable storage configuration and appropriate credentials
(or run `cloud-app files ...` inside a configured pod). Storage credentials and
workflow submission credentials are separate.

Build the native utility and pinned tools from the repository root:

```sh
bash Applications/CubeAndConquer/build-tools.sh
export LEAN_CLOUD_SAT_TOOLS="$PWD/.lean-cloud/sat-tools/bin"
cd Applications/CubeAndConquer
lake build cloud_app sat_files sat_tests
.lake/build/bin/sat_files prepare storage.json problem.cnf input.json
.lake/build/bin/sat_files run storage.json input.json > report.json
.lake/build/bin/sat_files verify storage.json report.json
```

`storage.json` is either a runtime node config or its `blobs` object. `run` uses
the direct interpreter for local diagnosis; distributed submission uses the cloud
console. `download CONFIG REF.json FILE` retrieves any referenced artifact.
`verify` exits 0 for a verified answer, 2 for inconclusive, and 1 for an error.
Outputs are not overwritten. `-` writes prepared JSON or downloaded bytes to stdout.
All binaries, checksums and source/license archives are included in the image.

## Resource policy and validation

Transfers use bounded buffers and CNFs are scanned without retaining all clauses.
Model checking retains an assignment array; native solvers/checkers manage their
own memory. Worker administrators can set:

| Environment variable | Default |
| --- | --- |
| `LEAN_CLOUD_SAT_INPUT_BYTES` | 1 GiB |
| `LEAN_CLOUD_SAT_PROOF_BYTES` | 16 GiB per cube |
| `LEAN_CLOUD_SAT_LOG_BYTES` | 256 MiB per stdout/stderr/model file |
| `LEAN_CLOUD_SAT_VARIABLES` | 10 million |

Use container memory, CPU, PID and storage quotas for hard isolation. File sizes
are monitored while tools run; the monitor can overshoot before killing a process,
so it is not a substitute for disk quotas. Limits are rechecked before publication.
Proof checking has its own deadline. Timeout kills/reaps the entire subprocess
group. Immediate cancellation of an arbitrary `Cloud.exec` is still a runtime
limitation; calls finish or hit their deadline. Cuber output is bounded to 16 MiB, JSON metadata
to 256 MiB, and text lines to 8 MiB (DIMACS clauses may span lines).

```sh
lake exe sat_tests --tools
# Repository root, with the built image:
bash Applications/CubeAndConquer/test-deployment.sh lean-cloud-sat:dev
```

Tests check uneven recursive splits and depth limits, compare generated programs
under direct/replay interpretation, stop after
every journal write, exercise interrupted and corrupted artifact transfers, compare
real solver results to exhaustive search, and reject forged proof bundles. The
three-worker integration test uploads CNFs, submits over HTTP, downloads evidence,
rechecks certificates and exercises the console without creating extra workers.
It removes its own containers and volumes on exit.
