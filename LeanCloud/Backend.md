# Shared backend contracts

The service model describes what the interpreter needs from a Db, leased queue,
and worker environment. Provider-specific details stay in adapters and deployment
configuration. The existing public replay interpreter runs unchanged on the
model and on real services.

## Individual operations

[`Backend/Contract.lean`](Backend/Contract.lean) defines typed requests and the
`Commits` relation. Each request has one atomic commit point. Its reply may arrive
later, or be lost when the caller crashes.

| Service | Required behavior |
| --- | --- |
| Db read | Observe the value at the read's commit point. A delayed reply keeps that observed value. |
| Db write | Successful writes persist the supplied value without changing other keys. Compatible retries succeed. Conflicting writes may be rejected; pure-workflow correctness must establish compatibility. |
| Enqueue | Accept a durable publication before reporting success. Repeated enqueue calls may publish the same location more than once. |
| Dequeue | Return idle or a previously published location with a delivery receipt. Order is unrestricted; deliveries may overlap or recur after acknowledgement. |
| Acknowledge | Settle the publication named by the receipt, or reject without changing it. A stale receipt may be accepted. Other publications remain unaffected. |

Acknowledgement discharges an obligation to deliver; it does not guarantee that
no further copy can arrive. Publication identities, receipts, and locations are
distinct. Two publications of one location must not be merged by payload equality.

The records and publication arrays are specification history, not required
service representations. `Backend.Laws` maps another representation to this
history and requires each committed primitive to satisfy `Commits`. These laws
contain no assumptions about a workflow's output.

## Requests and worker replacement

[`Backend/Execution.lean`](Backend/Execution.lean) separates issuing a request,
committing it, and delivering its reply. A call has a worker and attempt identity.
Crashing discards its continuation but retains an already-issued request. That
request may commit after a replacement has started. Its old reply cannot resume
the replacement's continuation.

`Execution.Transition` uses the service laws directly. `Execution.step` is an
executable instance driven by queue decisions. `step_refines` proves that every
accepted executable step is a contract transition; `lawful_commit` admits
operations from any representation satisfying `Backend.Laws`.

The [main equivalence theorem](Proofs/MainTheorems.lean) derives workflow
correctness over these transitions. No crash event is a `CloudError`. Infrastructure errors escape through the
backend monad, outside the recorded workflow-failure channel.

## Recovery and fairness

[`Backend/Recovery.lean`](Backend/Recovery.lean) states environment obligations
over contract-based traces:

- A continuously pending live request eventually commits, and an available live
  reply eventually arrives.
- A stopped logical worker is eventually replaced with the same program and input.
- While consumers keep polling, an unsettled publication eventually receives a
  delivery or acknowledgement.
- After some finite point, crashes stop and at least one logical worker exists.

There is no fixed restart count or maximum delay. The queue may use a visibility
timeout or a connection-bound lease; expiry is abstracted as permission to
redeliver. Retention, dead-letter recovery, and replacement capacity must sustain
these obligations for the supported run. The theorem derives sufficient finite
fuel from a completing execution prefix; a fixed budget cannot cover arbitrarily
long idle schedules.

Safety does not require fairness. Eventual completion does. The contract does not
assume that processing succeeds or that the desired result is eventually written.

## Same interpreter, shared adapter code

[`Backend/Replay.lean`](Backend/Replay.lean) connects typed requests to the public
`LeanCloud.interpret`, `JournalDb`, and `LeaseQueue.toWorkQueue`. Completion is an
ordinary Db record, using the same `CompletionStore` code as the real worker.
No special simulator completion field bypasses journal reads or writes.

The executable model is proved to satisfy the primitive laws in
[`Backend/Model.lean`](Backend/Model.lean). Generated pure workflows compare direct
evaluation with replay under three-worker schedules containing crashes, late
commits, and duplicate deliveries.

[`Backend/Check.lean`](Backend/Check.lean) checks sequential observed operations
against this model. It retains multiple possible histories when identical queue
payloads leave the publication identity ambiguous. Its present scenarios use
compatible writes. Checking arbitrary concurrent invocation/response histories
would additionally require a linearization search.

[`BackendAdapterLaws.run`](../LeanCloudTests/BackendAdapterLaws.lean) applies the
same checker to supplied Db and queue adapters. The integration suite exercises
PostgreSQL and RabbitMQ and separately compares generated workflows on three real
workers. Other adapters can use this suite when implemented. Tests provide
evidence; they cannot prove an external service or unbounded fairness.

## Workflow guarantees

[`concurrent_replay_matches_direct`](Proofs/MainTheorems.lean) now uses these
contracts. For a supported pure workflow, lawful codecs and comparisons, and a
fair execution whose crashes eventually stop, every worker eventually returns
the direct interpreter's outcome with enough finite fuel. That same outcome is
stored in the completion record. The theorem derives the completing prefix and
the fuel bound; it does not assume either.

Safety covers every legal execution without fairness: recorded outcomes agree
with direct evaluation, and a worker can return only that outcome or fuel
exhaustion. Liveness additionally uses continued polling, fair delivery and
recovery. The proof derives successful processing from the actual interpreter.

The proof covers publication before acknowledgement, no loss of unfinished
work, duplicate deliveries after acknowledgement, and late orphaned commits.
Each outstanding request can commit at most once; new retries are new requests.
No bound on an orphan's delay is imposed. After the final crash there are only
finitely many orphaned requests, so a suffix exists without further orphan commits.

[`BackendRealization.lean`](Proofs/BackendRealization.lean) connects the repeated
iteration proof to the public fuel-based interpreter. Administrative iteration
boundaries disappear. Private request ids may be renamed because the real loop
can issue its next request earlier; corresponding calls retain their operation,
reply and worker generation, and every boundary retains the same service state.

The theorem covers ordinary pure values, bind, delay, failure and parallel.
Arbitrary exec/IO, blobs, cancellation, changing workflow binaries, lost durable
data and permanent infrastructure failure remain outside this guarantee.
Provider adapters must satisfy the primitive contracts; tests can find violations
but do not prove an external implementation or its unbounded fairness.
