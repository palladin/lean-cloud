# Interpreter tests

Run everything from the repository root:

```sh
lake test
```

The suite currently contains 515 named cases. Some cases also iterate over values,
fuel budgets, journal writes, or queue updates. There are no additional test
dependencies. Any failure prints its test name and exits with a nonzero status.

Use `--` to pass arguments through Lake to the test runner:

```sh
lake test -- --list
lake test -- differential/parallel/
lake test -- generated/seed/42
lake test -- replay/checkpoints/ replay/fuel/
lake test -- queue/
```

Filters are test-name prefixes; multiple filters select their union. A filter that
matches nothing fails rather than silently succeeding.

## What the comparison checks

[Support.lean](Support.lean) runs the same `Cloud` program against two fresh copies
of the same model backend. `DirectInterpreter.interpret` supplies the expected
behavior through structural recursion, without fuel or a scheduling policy.
Replay receives enough fuel and a model queue that selects pending locations in
numeric path order. That policy reproduces the direct interpreter's array order.

Each differential case compares:

1. The final value, or the complete typed `CloudError`.
2. The ordered primitive-effect trace, including arguments and execution counts.
3. Blob contents, names, and allocation state.
4. A second run with the retained queue and journal: the outcome must be the same, with no
   new primitive effects or changes to recorded outcomes.

The journal is interpreter bookkeeping, so its contents are not compared with the
direct interpreter. Instead, the tests require the direct interpreter to make no
journal reads or writes. Blob allocation uses fresh keys to make duplicate writes
observable.

Each replay step advances one primitive effect, fork, join, or completion.
Other queue policies can interleave effects across branches, including nested groups.
Both interpreters
run every child even after a typed failure, and then select the first failure in
array order. Result order is also independent of completion order. Known-result
and known-effect-order assertions check the oracle as well: agreement alone could
miss a bug in shared primitive execution.

[WorkQueue.lean](WorkQueue.lean) tests replay with first, last, scripted, and
reproducible pseudorandom selection policies implemented by the environment.
Explicit scripts check interleaved effect order. Generated programs with
schedule-independent results are compared with direct evaluation under three
policies; their effect multisets must match after normalizing blob allocation
order. A shared-counter example deliberately produces different results under
different policies: arbitrary schedules need not agree with sequential execution.
A completed environment must return its final outcome without selecting more work.

## Coverage

| Module | Checks |
| --- | --- |
| [Pure.lean](Pure.lean) | Recorded pure calculations, captured inputs, dependent binds, parallel pairs, blob inputs, cached values, and the Id backend. |
| [Differential.lean](Differential.lean) | Pure values, delays, mixed result types, captured values, data-dependent control flow, heterogeneous `\|\|`, empty/single/wide/nested/successive parallel groups, continuation chains, failure order, blob operations and errors. |
| [Generated.lean](Generated.lean) | 256 reproducible generated programs combining binds, branches, delays, effects, blobs, failures, and parallel groups; all 32 ordered two-leaf compositions under bind and parallel. |
| [Replay.lean](Replay.lean) | Restart after every journal write in selected workflows, fuel exhaustion, cached results and failures, rejected writes, malformed records, and selected divergence checks. |
| [Codecs.lean](Codecs.lean) | Codec round trips, malformed input rejection, binary data, journal records, and an explicit broken-codec counterexample. |
| [Backends.lean](Backends.lean) | Separate Db and blob interfaces over `Id` and `IO`, returned backend handles, state-dependent effect results, native exceptions, deep parallel nesting, and location navigation. |
| [WorkQueue.lean](WorkQueue.lean) | Scripted interleaving; state-dependent results; nested pending work; error and result ordering; heterogeneous pairs; empty groups; numeric location order; 128 generated programs under three policies; restart under a different schedule; interruptions around every queue update; temporary idle responses. |

Generated failures print both the seed and the program tree. The generator uses
fixed seeds, so the same test can be rerun with a prefix such as
`generated/seed/42`.

## Recovery boundaries

The checkpoint tests first obtain an uninterrupted baseline. For each journal
write in that run, they start again from an empty journal and inject an exception
immediately after that write commits. They discard the interrupted interpreter
call and restart using the retained queue and backend state. The recovered outcome, effect
trace, backend state, and final journal must match the baseline. The workflows
include nested groups, blobs, typed failures, and an empty group.

Fuel tests repeat this comparison for initial budgets 0 through 79, then resume
with enough fuel to complete.

Queue recovery tests also interrupt every journal write, including the gap
between completing a child and updating its parent's slot. They resume with a
different pseudorandom schedule. These fixtures use schedule-independent results
and unique effect labels: the output and final journal must match, and the effect
multiset must be unchanged even if execution order differs. In general, changing
the schedule can change results when effects share mutable state.

Queue-update tests interrupt immediately before and after every atomic publication
of successor locations or the final outcome. Restart must retain pending work and
avoid repeating committed effects. An idle response is not treated as completion;
an environment with no work is never silently reseeded by the interpreter.

An effect can execute before its outcome is committed. A separate test interrupts
that gap and checks that replay executes it again. This suite therefore does not
claim exactly-once external effects across that boundary.

Native `IO` exceptions escape both interpreters and stop the current execution.
They differ from typed cloud failures, whose outcomes are collected and recorded.

## Adding a case

Use `expect` for a program with a known result. It also runs the full differential
comparison and the second replay:

```lean
expect "parallel/captured-input" (fun ref => cloud {
  let n ← execValue ref "input" 4
  Cloud.parallel #[pure (n + 1), execValue ref "right" (n * 2)]
}) (.ok #[5, 8])
```

Use `checkpointSweep program` to restart after every committed journal write, or
`fuelSweep program` to test interrupted prefixes. New case collections must be
included in `allCases` in [LeanCloudTests.lean](../LeanCloudTests.lean).

## Scope

These tests exercise simulated interleaving on one thread and ideal in-memory
storage. They do not test concurrent workers, duplicate queue delivery, database
adapters, cloud deployments, or cancellation. Choice has only an explicit
unsupported-operation check.

Differential comparison assumes the queue selects the sequential reference order,
enough replay fuel, stable program/input, and codecs that round-trip persisted values.
The direct interpreter does not serialize
values, so a broken codec can make replay fail while direct execution succeeds;
the suite demonstrates that distinction.

The separate [equivalence theorem](../LeanCloud/Proofs/QueueContract.lean) proves
equal results/errors for pure `Cloud Id` programs containing ordinary pure values,
delay, failure, and parallel. It uses an ideal Db and a lawful fair queue, permits
arbitrary pending-item selection, and derives sufficient fuel. It has no external
user state or effect-order assumptions.

The theorem covers fresh runs with serialized worker steps. Exec (including the
recorded `Cloud.pure` helper), blobs, restart correctness, simultaneous workers,
and real adapters are outside its scope. The tests above still exercise these
runtime effects and modeled recovery scenarios.

[Queue laws](../LeanCloud/Proofs/WorkQueue.lean) specify valid selection, retention,
completion reporting, and weak fairness. Finite tests check representative
schedules; they do not prove backend fairness.
