# Simulating the scheduler and workers

`SimM` is lean-eff's freer computation over atomic environment operations.
`Cloud (SimM World)` uses the ordinary Cloud effects. The replay interpreter runs
unchanged: storage and mailbox operations suspend its `SimM` continuation.

Actor zero is the scheduler; the other actors are workers. Their programs call
`Scheduler.turn` and `Worker.turn`; the deployment pool wraps the same recursive
scheduler and replay worker with multi-run routing and ownership checks. The model
world contains global immutable records and user blobs, private scheduler state,
durable mailboxes, unacknowledged deliveries, confirmed publications awaiting
delivery, and worker observation metadata. That combined
model is not a deployed shared service.

An external driver chooses events:

- `commit`: execute one atomic operation and retain its reply.
- `resume`: deliver that reply and evaluate until the next operation.
- `crash`: discard the actor's continuation.
- `restart`: create a fresh continuation and consumer session for the same actor mailbox.
- `commitOrphan` / `discardOrphan`: settle a remote request left by a crash.
- Mailbox delivery, duplication, delayed delivery, and scheduler timer ticks.

A confirmed message survives actor failure. Receiving reserves it; acknowledgement
removes it. Consumer failure requeues unacknowledged deliveries. Old session
receipts cannot acknowledge a replacement consumer’s delivery.

Scheduler crashes discard the traversal, tickets and inspection tree. The catalog
retains attempt counters and known worker identities. On startup,
`Scheduler.recover` requests cancellation; only after the old workers acknowledge
stopping can root replay reconstruct progress. No saved partial join is needed.
Worker crashes discard local observations of record keys; confirmed reports and
global records still survive independently.

A pending remote blob write can commit after its worker crashes. Its continuation
cannot run again. A pending local scheduler database operation dies with the
process; a committed database write survives even when its reply is lost. This
prevents an old local save from overwriting state after scheduler restart.

The scheduler's catalog commits and the blob service's committed records
are separate atomic operations. There is no transaction across those services.
Retries, immutable records, and attempt numbers bridge their failure windows.

Generated tests run finite periods of faults, then keep delivering messages,
advancing expiry time, and scheduling live actors. They compare the durable root
result with the direct interpreter and check warm replay. Targeted cases kill
actors before and after record creation, scheduler saves, and message sends.

Finite actor/interpreter budgets make simulation executable. Reaching a simulation
budget is not workflow completion. Tests require the scheduler to finish and the
expected root record to exist. These tests are evidence, not a general liveness
theorem.

The [semantic theorems](Proofs/MainTheorems.lean) compare direct evaluation with
sequential replay, parallel replay, and worker-local restarting parallel replay
over a pure journal. They establish the meaning
of recording, location-based resumption, and fork/join. Scheduler and worker
coordination, crashes, delivery, and recovery are implementation concerns covered
by these simulation tests and the real adapter and container tests.
