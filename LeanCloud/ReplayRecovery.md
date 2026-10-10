# Worker-local restart

[RestartingParallelReplay.lean](RestartingParallelReplay.lean) runs the ordinary
`ReplayInterpreter.step`. Only workers read and write replay records.

Each spawned worker executes:

```text
restart locally:
  step(program, input, assignment)
  if completed: read its recorded outcome and return done(outcome)
  if suspended: return fork(location, count)
```

A crash discards the worker's continuation and retries the same assignment with
its surviving records. The interpreter budget resets on each attempt; the retry
budget limits the number of attempts. Application errors and interpreter budget
errors are not crashes and do not trigger retries.

The scheduler handles replies: it schedules children for `fork`, then schedules
the parent again. The root worker's `done(outcome)` supplies the final result;
the scheduler never reads the journal to retrieve it. Scheduler crashes,
redispatch, and service availability belong to runtime tests, outside this model.

## Durable state

[ReplayFaults.lean](ReplayFaults.lean) injects faults before or after a worker's
atomic storage reads and creates. Before an operation, the old state survives.
After a write, the new record survives even though its acknowledgement is lost.

Workers read the same immutable old journal and return only their new records.
The storage model waits for all workers and unions their disjoint additions,
including partial progress from a worker whose retry budget ran out. Overlapping
writes are invalid even if their values match. This union models durable storage;
it is not a scheduler write.

There is no scheduler fault script, checkpoint, or outer restart wrapper.

## Example

```lean
import LeanCloud.RestartingParallelReplay

open LeanCloud ReplayFaults
open RestartingParallelReplay (interpret)

def workflow (n : Nat) : Cloud WorkerM Nat := cloud {
  let values ← Cloud.parallel #[
    Cloud.pure (fun _ => n * n),
    Cloud.pure (fun _ => (n + 1) * (n + 1))]
  return values.foldl (· + ·) 0
}

def faults : Plan := {
  workers := [(Location.root.child 0,
    [⟨.create (ReplayStore.valueKey (Location.root.child 0)), .after⟩])] }

#eval ((interpret 1000 workflow 7).run (Saved.initial faults)).1
-- Except.ok 113
```

A scripted fault fires once at its next matching operation. Unreachable faults
do not fire. Scripts and counters survive retries. After fuel exhaustion, pass
the returned `Saved` to another call with more fuel to retain progress.

## Verification

[WorkerRestart.lean](Proofs/WorkerRestart.lean) proves local storage laws:

- Reads preserve the journal, including interrupted reads.
- Interrupted writes preserve old records and the worker's write region.
- With more attempts than scripted faults, retrying a read or create returns
  exactly the result and journal of one uninterrupted operation. An acknowledged
  or unacknowledged committed create is not duplicated.

[RecoveryWorker.lean](Proofs/RecoveryWorker.lean) lifts these laws to the whole
`ReplayInterpreter.step` and its final result read. A retry starts at the branch's
entry, reconstructs from surviving records, and preserves all committed writes.

The third theorem in [MainTheorems.lean](Proofs/MainTheorems.lean),
`restarting_parallel_replay_matches_direct`, covers the complete restarting
driver: the same finitely evaluating pure program returns the same value or
application error as direct evaluation, from empty storage, for any finite worker
fault plan and every sufficiently large fuel budget. It proves completion rather
than assuming a successful replay run. Codecs must round-trip, and parallel
workers' writes are proved disjoint.

Run `lake exe lean_cloud_tests restarting-replay`. Tests check worker-local
suspension and completion replies, both sides of storage boundaries, preserved
siblings, exhausted-run resumption, application errors, and 128 generated pure
workflows against direct and sequential interpretation. Runtime scheduler
recovery and deployment availability remain outside this semantic theorem.
