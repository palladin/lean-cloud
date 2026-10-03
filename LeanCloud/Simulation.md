# Simulating workers

`SimM` is the original executable simulator for atomic state operations and timed
leases. It remains useful for tests and focused proofs. The main concurrent
[workflow theorem](Proofs/MainTheorems.lean) now uses the broader
[shared backend contracts](Backend.md), which also permit duplicate delivery
after acknowledgement and requests that commit after their caller crashes.
The two drivers use the same public replay interpreter; their execution models
have different permitted behaviors.

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

This simulator uses the actual `JournalDb` and `LeaseQueue.toWorkQueue` adapters.
Each physical Db get/put, queue operation and completion access is separately
atomic. Multi-key reconstruction and publication before acknowledgement are not
single transactions. The write history is proof metadata, not an adapter API.

Its timed queue rotates receipts on redelivery. Its crash event discards a
pending atomic operation. These are particular choices of this simulator; the
shared model additionally allows stale receipts to succeed, post-acknowledgement
duplicates and late commits from abandoned requests. See
[Backend/Execution.lean](Backend/Execution.lean) for that request lifecycle.

The narrower simulator's proofs remain in `Proofs/Concurrent*.lean`:

- Journal publication, reconstruction, child completion and wakeups remain safe
  under interleaved commits and delayed replies.
- Every acknowledgement follows publication of replacement work or the final
  result. Unfinished work retains an outstanding queue item.
- Fair worker actions and delivery after recovery imply completion; sufficient
  finite fuel realizes the completing execution prefix.

The main theorem in [MainTheorems.lean](Proofs/MainTheorems.lean) derives these
workflow guarantees directly from the broader primitive contracts. Its current
supporting proofs are `Proofs/Backend*.lean`; the
[proof guide](Proofs/README.md) explains the assumptions and reading order.

[Simulation tests](../LeanCloudTests/Simulation.lean) exercise two-worker
schedules, sibling completion races, lost replies, stale receipts, and crashes
at backend boundaries. [Backend contract tests](../LeanCloudTests/BackendContracts.lean)
exercise the broader model, including late orphan commits and duplicate delivery.
Both compare pure workflows with direct interpretation. Integration tests also
compare generated workflows with concurrent real workers.

Neither model executes arbitrary external IO as part of the pure-workflow proof.
Preemption occurs at backend request boundaries; intervening pure computation
runs together. Service implementations are assessed through conformance tests;
finite tests do not prove unbounded fairness or external-service correctness.
