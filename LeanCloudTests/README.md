# Tests

```sh
lake build
lake test
cd runtime && lake exe cloud_inbox_tests
```

The three semantic theorems are checked by `lake build`.
`ProofExamples.lean` applies all three to a nested parallel workflow.
Generated programs compare DirectInterpreter with sequential, parallel and
restarting replay. The runtime model adds scheduling, worker isolation, crashes,
restarts, membership changes and durable completion. Seeded programs cover
captured inputs, dependent binds, blobs, delay, failure and nested/empty parallel
arrays. Results and failures preserve source order.

`PoolModel` tests three workflows on three workers across 64 seeds with 400
operations each. Checks include attempt ownership, pause/resume/kill, expiry and
renewal, late/duplicate reports, orphan writes and immutable records. Programs
finish after faults stop and their results agree with direct evaluation.

`cloud_inbox_tests` exercises real HTTP and SQLite, including 32 × 200 mailbox
model operations, SIGKILL recovery, stop barriers, fencing, lease renewal,
temporary inbox reclamation, authentication and registry APIs. Storage tests
cover immutable writes, request failures, credential refresh, paginated cleanup
and missing/malformed telemetry.

Replay-cache tests compare the actual interpreter's results, journals and
ownership checks with caching disabled and enabled, and count backing-store
reads. They cover byte/entry bounds, canonical writes, missing values, failures,
revocation on cache hits and removal racing with an in-flight operation.
Cleanup tests cover every worker, partial failure and retry, late telemetry,
and run isolation. Docker tests stop an active worker during removal, verify
that the CLI retains its retry request, and inspect all nodes after retry and
after a scaled-down node returns.

## Console and helpers

CLI logic runs in Eff against a pure HTTP/file/terminal host. It has no general
process-launch effect. Tests cover workflow commands, API identity and credential
rotation, pagination, retry identities after uncertain responses, watch/top,
source metadata, saved final views, help/completion and the anchored terminal.
The same client accepts loopback HTTP and remote HTTPS endpoints.

```sh
bash deploy/test-helpers.sh
```

Offline helper contracts check parameterized Compose/Kubernetes files, pinned
images, distinct credentials, private endpoints, retained volumes, missing-state
rejection, stop barriers and retryable explicit deletion. ShellCheck runs in CI. The external deployment
helpers replace tests for removed CLI provisioning commands.
Generated applications inherit Git/Docker exclusions for credentials and state.
CI also checks Docker's actual context filtering with dummy private files using
`bash deploy/test-build-context.sh`.

## Isolated Docker integration

```sh
bash deploy/tests-prepare-app.sh
docker buildx bake -f .github/docker-bake.hcl
lake build lean_cloud cloud_console_tests
lake exe cloud_console_tests --pool-only
lake exe cloud_console_tests --maintenance-only
lake exe cloud_console_tests --scaling-only
lake exe cloud_console_tests --chaos-only
```

Each suite creates its own Docker project using `deploy/local.sh` and removes
its containers/volumes afterward. Every workflow operation uses the scheduler
HTTP API. The tests cover:

- Catalog, submission, source, metrics, result, removal and durable restart.
- A fresh client with no checkout access, including a final view after deleting
  every client-side cache.
- Pause/resume/kill with another workflow continuing on the shared pool.
- Zero capacity, growth and shrink through the helper's stop/start barrier.
- Uncaught user IO exceptions complete as recorded failures without restarting
  any node; the same pool continues serving other workflows.
- Generated pure workflows, including failures, compared with DirectInterpreter
  after journal storage outages, a worker network partition, a scheduler pause,
  and six seeded crashes.
  Checks cover the stop barrier, stale/duplicate messages, immutable confirmed
  records and completed results surviving another scheduler crash.

Deployment setup and fault injection use Docker explicitly in the test driver;
they are not CLI commands. Failure logs remain under `.lean-cloud/lean-cloud-*/`.
CI builds both images together with a shared Buildx cache, then runs independent
suites concurrently. These local tests do not provision cloud resources.
Run the same HTTP client checks against a separately deployed cluster:

```sh
lake exe cloud_console_tests --remote /tmp/cloud-test-client http://127.0.0.1:8080 .kube-deployment/client.token 4
```

This test requires the demo registry and unused `remote-1`, `remote-paused`, and
`remote-killed` workflow IDs. It checks four nodes (one scheduler and three
workers), blobs, pause/resume/kill, and removes its test workflows. It never
provisions or removes infrastructure. Run through a
private port-forward or supply an authenticated HTTPS endpoint.

The original Compose adapter fixture is also available:

```sh
docker compose run --build --rm checks
```

It compares generated workflows using the real S3/HTTP/SQLite adapters against
direct evaluation and exercises mailbox redelivery and durable result publication.
The stress model is available with `lake exe cloud_stress_tests`.
