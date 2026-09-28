# Interpreter equivalence

[`same_output`](QueueContract.lean) proves that the actual replay and direct
interpreters return the same value or `CloudError` for a pure workflow and the
same input. It derives eventual completion and a sufficient fuel budget for any
lawful, fair queue.

The theorem covers `Cloud Id` programs built from ordinary `pure`/`return`, bind,
`delay`, `fail`, and `parallel`, including nested and empty parallel groups.
[`PureProgram`](Assumptions.lean) describes this fragment and requires the codecs
inside parallel requests to round-trip. The final result codec must also
round-trip. Parallel results and failure priority follow array positions,
regardless of the order in which branches finish.

There is no external user world, effect trace, or commutation assumption. The
direct side produces only `Except CloudError α`. The replay model contains the
interpreter's Db records, pending locations, and final completion record.

Runtime `Cloud.exec` and blob operations remain available but are outside this
theorem. The recorded `Cloud.pure (fun _ => value)` helper also uses exec, so it
is outside the current fragment; ordinary monadic `pure value` is included.

| Part | What is proved |
| --- | --- |
| [Evaluation](Evaluation.lean) | Pure evaluation agrees with the actual direct interpreter, without using blob operations or changing its backend handle. |
| [Replay snapshot](ReplaySnapshot.lean) | Records and partial child results correspond to the original program. |
| [Pending locations](SnapshotRouting.lean) | A pending location belongs to its original branch and has an open parent, so the worker's location checks pass. |
| [Worker step](SnapshotStep.lean) | Processing any pending location preserves the snapshot, updates the correct parent slot, and publishes exactly the next pending work. |
| [Snapshot work](SnapshotWork.lean) and [work bound](SnapshotWorkBound.lean) | Completion yields the program's pure evaluation. A partial snapshot cannot consume more work than the completed program; an unfinished snapshot has work remaining. |
| [Fair driver](FairDriver.lean) | Fair selection eventually completes the workflow, giving a finite execution and enough fuel for the public interpreter. |
| [Queue contract](QueueContract.lean) | These results follow from primitive polling and acknowledgement laws, without assuming that a completed execution already exists. |

`Db` is modeled as an exact map: reads return the addressed record and writes
replace that record successfully. A queue chooses a pending location, idles, or
reports a recorded completion. Acknowledgement applies the interpreter's
published response. Fairness rules out indefinitely ignoring pending work.

A fork, join, or terminal report consumes processing work. The same
[work relation](EvaluationWork.lean) serves two purposes: with delay cost `0`,
it counts queue progress; with delay cost `1`, it also counts delays and proves
that reconstruction terminates. The sufficient fuel bound may depend on the
schedule.

The theorem starts with an empty Db and the root work item. Worker calls are
serialized; crash recovery, simultaneous workers, real database/queue adapters,
choice, and cancellation are not covered. The runtime tests exercise additional
behavior outside this proof's scope.

Run `lake build` to check the proofs. They contain no `sorry` or custom axioms.
