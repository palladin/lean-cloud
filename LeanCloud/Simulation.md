# Simulating workers

[Simulation.lean](Simulation.lean) schedules the backend calls made by workers.
[SimulationBackend.lean](SimulationBackend.lean) connects it to the existing
replay interpreter, physical journal, and leased queue.

There are two effect languages, both using `lean-eff`:

```lean
Cloud m α = EffF (Control m) α
SimM δ α  = EffF (Atomic δ) α
```

`Cloud` describes the workflow. The replay interpreter handles it and calls the
Db and queue. Their simulated implementations produce atomic requests in `SimM`.
The external driver executes those requests against shared state. In a real
backend the interpreter instead runs over `IO`.

## A worker attempt

For example, this workflow captures `input` in both parallel branches:

```lean
import LeanCloud

open LeanCloud

def workflow (input : Nat) : Cloud SimulationBackend.M Nat := cloud {
  let (x, y) ← cloud { return input + 1 } || cloud { return input + 2 }
  return x + y
}

def start (_ : Fin 2) :=
  SimulationBackend.attempt 10000 100 workflow 7

def initial :=
  Simulation.State.initial SimulationBackend.initial start

def paused :=
  Simulation.run start SimulationBackend.advance
    [.commit 0, .commit 1, .resume 1] initial
```

The interpreter fuel is `10000`; the lease duration is `100` clock units. Worker
IDs are `Fin 2` here; the driver supports any fixed number of workers.

Both workers first read the durable completion record. This schedule commits
those reads, delivers worker 1's reply, and leaves worker 0's reply pending.
No clock time passes automatically. The returned state can be supplied to another
`Simulation.run` call to continue the schedule.

An attempt has type:

```lean
SimM SimulationBackend.Durable
  (Except CloudError Nat × SimulationBackend.Worker)
```

The inner worker handle contains local state such as the current receipt. Its
state is captured by the suspended interpreter continuation. Shared journal and
queue state live only in the simulation machine and are read at each commit.

## External events

| Event | Meaning |
| --- | --- |
| `commit worker` | Execute one waiting atomic operation and save its response. |
| `resume worker` | Deliver that saved response; evaluate until the next request or return. |
| `crash worker` | Discard a running worker's continuation, local state, and any pending response. |
| `restart worker` | Replace a stopped worker with `start worker`, using fresh local state. |
| `advanceTime elapsed` | Advance the queue clock without deleting messages. |

Switching workers needs no separate event. A worker remains paused while the
driver selects other workers. A delayed read response retains the value observed
at commit; resuming does not reread storage.

Crashing a waiting worker models interruption before an operation. Committing
and then crashing before resume models interruption after commit with a lost
reply. Neither crash nor restart releases leases, clears records, or seeds another
root message. Time advancement permits expiry and later redelivery. A paused
worker can also outlive its lease while another worker processes a newer delivery.

Invalid events, such as resuming before commit or restarting a live worker, return
a simulation `Error`. Script exhaustion leaves the machine paused. Neither is a
workflow `CloudError` or evidence of workflow completion. The test driver's event
budget is likewise separate from interpreter fuel.

## Guarantees and limits

The simulation uses the actual `JournalDb` and `LeaseQueue.toWorkQueue` adapters.
Every physical get, put, enqueue, dequeue, completion-record access, and
acknowledgement is separately atomic. A journal read is not a transaction or a
snapshot across keys, and publication is not atomic with acknowledgement.
The ideal raw Db retains a newest-first write log; lookup returns the latest
value. Keeping old entries lets the proofs order observations without adding
transactions. This log is model history, not a requirement for production storage.

[Proofs/Simulation.lean](Proofs/Simulation.lean) proves retention of saved replies
and replacement of only the crashed worker on restart. The same model covers one
worker or many; crash and restart are external events, separate from workflow
errors. The main [equivalence theorem](Proofs/ConcurrentEquivalence.lean) proves
completion, returned output, and durable output for pure workflows under the
fairness and fuel conditions described below.

[ConcurrentJournal.put_concurrent](Proofs/ConcurrentJournal.lean) proves safety of
concurrent calls to the actual `JournalDb.put`, including partial child arrays
and completed results. Every finite legal schedule preserves records; every
finished call succeeds with all its intended records present. Initial records
and all intended writes must agree with one expected journal, with reflexive JSON
comparison on the written values. Publication can stop partway through, and a
saved absent-key response can be delivered after another worker has written.
The reusable rule in [SimulationSafety.lean](Proofs/SimulationSafety.lean) keeps
these commit and response-delivery boundaries separate.

[ConcurrentJournal.get_concurrent](Proofs/ConcurrentRead.lean) proves read
reconstruction when the expected records are well formed and background workers
satisfy the journal-preservation safety rule. Cached results and present child
outcomes are backed by durable records; missing slots were absent before the read.
Independent read/reply boundaries allow a returned array to mix observations
from different times. It need not equal the journal at any single instant, and it
may lag behind writes committed during the read. Crashes and restarts preserve
the lower bound from the beginning of the schedule.

[ConcurrentTree.lean](Proofs/ConcurrentTree.lean) derives readable encodings,
admitted slot values, and cache/child consistency from a pure program's execution
tree, and uses them in the actual completion proof.
[ConcurrentStep.lean](Proofs/ConcurrentStep.lean) extends this to the actual replay
step, including reconstruction, ancestor completion races, fork creation, and
joins. Activated input locations produce activated successors or the program's
own final outcome under arbitrary finite step schedules, crashes, and retries.
The traversal fuel bound comes from the original tree. The loop proof below
also handles budgets too small to reach that bound.
These theorems do not require fairness or claim eventual completion.

[LeasedStep.lean](Proofs/LeasedStep.lean) connects that step proof to the actual
leased Db adapter. Its `leased_step_checked` theorem preserves the worker's
delivery receipt and the original program's response contract. The proof retains
all atomic operation/reply boundaries; it does not make a whole step atomic.

[ConcurrentQueue.lean](Proofs/ConcurrentQueue.lean) proves that the actual `next`
and `complete` calls preserve activated queue payloads and the original final
outcome. Successors may be consumed concurrently, and a delivered receipt may
already be stale. The invariant covers visible and leased messages. This is a
safety result; ConcurrentNoLoss below proves that unfinished work also retains
an outstanding queue item.

[ConcurrentLoop.lean](Proofs/ConcurrentLoop.lean) composes the actual worker loop
and proves safety of finite schedules starting from `SimulationBackend.initial`.
Workers can crash independently and restart with fresh receipts. Every retained
message remains activated, the final-result field agrees with the original
workflow, and every returned worker result is that workflow's decoded outcome
or fuel exhaustion. The proof permits arbitrary interleaving of commits and
saved replies; it does not require serialized worker steps.

[ConcurrentRecovery.output_safety](Proofs/ConcurrentEquivalence.lean) compares
these results with the actual direct interpreter on the same pure program and
input. Direct evaluation issues no simulated operations. Replay either agrees
with it or reports fuel exhaustion. `ConcurrentRecovery.output_agreement`
excludes that exhaustion alternative when the worker's fuel exceeds the pure
program's traversal bound plus the number of events in the finite schedule.
This bounds a returned result; it does not promise that the prefix returns.
`ConcurrentRecovery.same_output` additionally derives a completing prefix and
sufficient fuel under fair delivery and scheduling after crashes stop.

[ConcurrentJoin.lean](Proofs/ConcurrentJoin.lean) connects publication to the join
reread: a last-child publication completes a group whose siblings are already
durable, even from a stale partial snapshot. Once completion is durable, the
actual reader returns that outcome and `finish`'s final decision requests the
parent as runnable. This assumes compatible records and a matching cached outcome
if one appears.

[ConcurrentFinish.lean](Proofs/ConcurrentFinish.lean) now composes the whole actual
`finish` call across arbitrary finite schedules, crashes, and retries. Every
returned call succeeds with its own outcome durable. A child wakeup has durable
parent-completion evidence; an empty response comes from a reread that began
with the child's slot present and the parent incomplete. Preconditions include
compatible, well-formed records, consistent caches, comparison reflexivity, and
the durable parent descriptor. The current command must be terminal or already
durably complete.

[ConcurrentWakeup.lean](Proofs/ConcurrentWakeup.lean) proves that if every child
of a nonempty group returns from its actual `finish` call, at least one requests
the parent. Retries may change their replies. Each empty reply has a reread point
with its own child slot present; the latest of these points would contain every
child, so the replies cannot all be empty. This covers notification under the
same storage assumptions, rather than eventual return or queue publication.

[ConcurrentPublication.lean](Proofs/ConcurrentPublication.lean) proves no loss
during a batch of actual queue publication requests: each incoming message is
retained until replacement work is durable. Returned requests have published
their successors or final outcome and cleared the receipt. The batch fixes its
incoming slots; overlapping requests for the same slot must agree on replacement
work, and all final-result writes must agree. This stage leaves new successors
for later consumers. Request retries may reuse a stale supplied receipt; the
full-worker restart protocol still discards local state and reacquires work.

The new handoff tests exercise that full protocol around enqueue, acknowledgement,
and final-result writes, before commit and after commit with a lost reply. They
also delay an empty reply until the parent is consumed and retry a crashed child
whose reply changes into a parent wakeup.

[ConcurrentHandoff.lean](Proofs/ConcurrentHandoff.lean) handles dynamic consumers:
each acknowledgement has evidence that all successors or the final result were
published first, even if another worker already consumed the successors. Slot
identities persist across redelivery and are never reused after acknowledgement.
[ConcurrentAudit.lean](Proofs/ConcurrentAudit.lean) connects this to the full
interpreter loop, deriving each removal's justification from a real delivery and
replay step. The proof covers every finite schedule and every point of an infinite
trace, including crashes with lost replies. Its history is proof data and does
not change the runtime.

The step proof now retains the evidence for each response in `StepProgress`.
[ConcurrentCoverage.lean](Proofs/ConcurrentCoverage.lean) proves local branch
coverage even when fork reads become stale before their replies arrive. It also
proves that an empty step response must come from a completed child with an
earlier incomplete-parent observation.

[`ConcurrentAudit.attempts_no_loss`](Proofs/ConcurrentNoLoss.lean) now proves that
every finite schedule has either the original workflow's durable final result
or an outstanding queue item, including leased items. The witness is not merely
a duplicate whose enclosing branch has already reported to a still-incomplete
group. Completed groups may still need a continuation wakeup. Successors have newer slots,
so responsibility transfers form a finite graph. That graph cannot end only in
empty child notifications: at a partial join, the latest missing child's reread
sees both its siblings' results and any results recorded before publication.
Crashes, retries, and concurrent consumption preserve this argument. Eventual
delivery and adequate fuel are still needed for workflow completion.

[ConcurrentLiveness.lean](Proofs/ConcurrentLiveness.lean) proves that the visible
journal eventually stabilizes in every actual concurrent trace. With that fixed
journal, [ConcurrentRank.lean](Proofs/ConcurrentRank.lean) proves that response
work cannot form a cycle: ordinary work advances through command locations,
while completed-ancestor wakeups decrease the number of enclosing completed
groups. Combined with no-loss, this supplies the structural completion argument.
ConcurrentCompletion now derives response closure from fair repeated-worker
execution. ConcurrentRealization supplies the completing prefix's finite fuel bound.

`ConcurrentAudit.delivered_publishes` connects fair worker actions to the actual
selected step: with adequate traversal fuel and no further crashes of that
worker, it eventually publishes its response. This holds even if the surrounding
attempt keeps running. Saved replies still require a resume event, and other
workers may consume successors as soon as they are published. Obtaining these
processing entries from real dequeue commits is proved in ConcurrentDelivery.
ConcurrentRealization derives sufficient fuel for the completing prefix.

`ConcurrentAudit.run_polls` now proves how the original worker reaches the code
selected by its poll reply. Fair scheduling carries the poll to a strictly later
boundary, retaining the actual continuation. For an item, it also supplies the
active replay location and the worker's receipt from a real dequeue. Idle and
completed replies keep their own continuations. This establishes the polling
transition; ConcurrentDelivery supplies fair item selection and
ConcurrentRealization supplies sufficient fuel.

[ConcurrentIteration.lean](Proofs/ConcurrentIteration.lean) now connects a full
poll/process/publish iteration to the original replay loop. With enough traversal
fuel, `run_iteration` reaches either its real recursive continuation or its result
continuation under fair worker scheduling. Publication is finished and the local
receipt is cleared first. Factoring an iteration preserves every backend request
and saved reply. Repeated iterations have a completion proof, and
ConcurrentRealization connects them to the actual loop with sufficient fuel.

[ConcurrentRepeated.lean](Proofs/ConcurrentRepeated.lean) provides a proof-only
view of continued polling: workers repeat the same actual iteration after
`.ok none`, retaining shared storage. Errors and terminal results cannot repeat.
A separate `repeatIteration` event represents the outer loop; it changes no
durable state or other worker. Worker fairness and repetition fairness give
iteration progress after crashes stop, and the existing no-loss invariant holds.
This avoids assuming a total polling budget at the start of the liveness proof.
`ConcurrentRepeated.eventually_completed` in
[ConcurrentCompletion.lean](Proofs/ConcurrentCompletion.lean) proves that fair
queue delivery, worker actions, and repetition make the correct final result
durable after crashes stop. `eventually_returns` proves each worker observes it.
Delivery is stated at actual dequeue commits, with acknowledgement and durable
completion as alternatives; processing is derived even for stale receipts.
The proof combines fresh-slot progress with the finitely many older slots.
[ConcurrentRealization.lean](Proofs/ConcurrentRealization.lean) realizes that
completing prefix in the actual fuel-based interpreter. Each worker needs fuel
greater than the traversal bound plus the repeated prefix's length. Only
administrative repeats disappear: commits, saved replies, crashes, restarts,
and clock advances retain their order and durable effects.

[`ConcurrentRecovery.same_output`](Proofs/ConcurrentEquivalence.lean) combines
completion with this realization. Given the same pure program and input, direct
evaluation and concurrent replay return exactly the same value or workflow error.
The final durable completion record must contain that same encoded outcome.
Fairness contains no successful-processing premise; the proof derives the
completing prefix and its fuel bound. The bound depends on the schedule.

`PublishedStep.successor` locates each published successor at a specific later
boundary of the original trace. It still works when that successor was consumed
before the publisher finished. This connects publication certificates to the
time when delivery fairness can apply.

`ConcurrentQueue.attempts_extend` proves that a legal finite schedule remains
legal with larger worker fuel budgets. The same commits, saved replies, crashes,
and restarts make exactly the same durable changes. Returned values are preserved
except for a smaller budget's exhaustion result; its extended computation stays
paused. This lemma preserves an established prefix while increasing fuel;
the completing-prefix argument is supplied by the theorem above.

[The tests](../LeanCloudTests/Simulation.lean) run the interpreter with two workers,
compare pure workflows with direct evaluation, explore bounded scheduling
prefixes, and interrupt every boundary of selected runs. They include concurrent
sibling completion, lost replies, stale receipts, and a parent completing while
another worker traverses an old child location.

The backend supplies no user blob operations, and arbitrary IO is not translated
into the simulation. Preemption occurs at backend boundaries; pure computation
between those boundaries is evaluated together.

[SimulationLiveness.lean](Proofs/SimulationLiveness.lean) models an infinite legal
trace and weak fairness for worker actions: a continuously enabled commit, saved
reply delivery, or restart is eventually scheduled. With this assumption, a
worker eventually returns after its own crashes stop. The proof follows the
actual suspended continuation; it assumes no successful worker output or queue
selection, and permits other workers to continue crashing.

[`ConcurrentRecovery.eventual_output`](Proofs/ConcurrentEquivalence.lean) applies
this to the real interpreter attempts: each eventually returns direct
evaluation's outcome or fuel exhaustion. This is attempt termination;
`same_output` uses fair queue delivery to derive completion and sufficient fuel.
A finished fuel-exhausted worker cannot use the existing
restart event, which only accepts stopped workers.
