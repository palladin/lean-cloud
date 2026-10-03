# Simulating the scheduler and workers

`SimM` is lean-eff's freer computation over atomic environment operations.
`Cloud (SimM World)` uses the ordinary Cloud effects. The replay interpreter runs
unchanged: storage and mailbox operations suspend its `SimM` continuation.

Actor zero is the scheduler; the other actors are workers. Their programs call
`Scheduler.turn` and `Worker.turn`, exactly as the real runtime does. The model
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
- Broker delivery, duplication, delayed delivery, and scheduler timer ticks.

A confirmed message survives actor failure. Receiving reserves it; acknowledgement
removes it. Consumer failure requeues unacknowledged deliveries. Old session
receipts cannot acknowledge a replacement consumer’s delivery.

On scheduler startup, the shared `Scheduler.recover` operation reloads its private
database and returns running assignments to pending. Completed jobs, partial
joins, and attempt numbers survive. Worker crashes discard local observations of
record keys; confirmed reports and global records still survive independently.

A pending remote blob write can commit after its worker crashes. Its continuation
cannot run again. A pending local scheduler database operation dies with the
process; a committed database write survives even when its reply is lost. This
prevents an old local save from overwriting state after scheduler restart.

The scheduler's persisted transitions and the blob service's committed records
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

Separately, [completed_replay_matches_direct](Proofs/MainTheorems.lean) proves
that scheduler completion implies a durable root result equal to direct
evaluation for pure workflows. It covers all actual finite Sim traces from empty
storage, including arbitrary crashes and message interleavings.

`concurrent_replay_matches_direct` additionally proves eventual completion given
sufficient interpreter fuel and recurring timely processing windows. A window
allows a delivered assignment to execute, its report to arrive
while the attempt is live, and the scheduler to save its transition. The proof
derives report success from the worker code and a single source-dependent fuel
bound. Other actors and broker events may interleave with the selected worker's
atomic operations. No successful report or correct result is assumed of the environment.
This is stronger than weak fairness or durable message delivery alone.

[WorkerProgress.job_can_report](Proofs/WorkerProgress.lean) supplies one progress
step: every reachable job can produce a fork or completion report in finitely
many uninterrupted commit/reply events, given sufficient fuel. This includes
reconstructing nested branches. Delivery and timely acceptance of reports are
separate obligations; the lemma does not assume they happen automatically.

[SchedulerDelivery](Proofs/SchedulerDelivery.lean) checks the receiving side:
an uninterrupted turn saves a selected live report's completion or child jobs,
confirms its reply, and acknowledges the input. The proof keeps those as
separate atomic operations and leaves replay values in worker-owned operations.

`ConcurrentSafety.completed_branch_persists` lifts completed-job preservation
through all subsequent actor and network events. Retries and recovery cannot
reopen completed work; `completion_persists` gives the same guarantee for the
whole workflow's finished status.

[CoordinationProgress.productive_intervals_bounded](Proofs/CoordinationProgress.lean)
proves a finite bound on useful scheduling work from the original pure source.
A live successful report increases a bounded measure; crashes and retries cannot
decrease it. Authorized joins cannot suspend again at the same fork.
[DeploymentProgress](Proofs/DeploymentProgress.lean) proves that the processing
windows are productive and that an unfinished run cannot contain infinitely
many of them. The run is sampled at finite batches of events; the window
assumption must hold at those sample points. Endless crashes, reports that
always expire before acceptance, and exhausted actor-loop budgets without
further processing opportunities are excluded by that assumption.
