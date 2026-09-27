# Interpreter tests

Run everything from the repository root:

```sh
lake test
```

The suite currently contains 364 named cases. Some cases also iterate over values,
fuel budgets, or every journal write in a workflow. There are no additional test
dependencies. Any failure prints its test name and exits with a nonzero status.

Use `--` to pass arguments through Lake to the test runner:

```sh
lake test -- --list
lake test -- differential/parallel/
lake test -- generated/seed/42
lake test -- replay/checkpoints/ replay/fuel/
```

Filters are test-name prefixes; multiple filters select their union. A filter that
matches nothing fails rather than silently succeeding.

## What the comparison checks

[Support.lean](Support.lean) runs the same `Cloud` program against two fresh copies
of the same model backend. `DirectInterpreter.interpret` supplies the expected
behavior; the replay interpreter receives a sufficiently large fuel budget.

Each differential case compares:

1. The final value, or the complete typed `CloudError`.
2. The ordered primitive-effect trace, including arguments and execution counts.
3. Blob contents, names, and allocation state.
4. A second run over the completed journal: the outcome must be the same, with no
   new primitive effects or changes to recorded outcomes.

The journal is interpreter bookkeeping, so its contents are not compared with the
direct interpreter. Instead, the tests require the direct interpreter to make no
journal reads or writes. Blob allocation uses fresh keys to make duplicate writes
observable.

The direct interpreter evaluates parallel children in array order, runs every
child even after a typed failure, and then selects the first failure in array
order. Both interpreters currently use these sequential semantics. Known-result
and known-effect-order assertions check the oracle as well: agreement alone could
miss a bug in shared primitive execution.

## Coverage

| Module | Checks |
| --- | --- |
| [Differential.lean](Differential.lean) | Pure values, delays, mixed result types, captured values, data-dependent control flow, heterogeneous `\|\|`, empty/single/wide/nested/successive parallel groups, continuation chains, failure order, blob operations and errors. |
| [Generated.lean](Generated.lean) | 256 reproducible generated programs combining binds, branches, delays, effects, blobs, failures, and parallel groups; all 32 ordered two-leaf compositions under bind and parallel. |
| [Replay.lean](Replay.lean) | Restart after every journal write in selected workflows, fuel exhaustion, cached results and failures, rejected writes, malformed records, and selected divergence checks. |
| [Codecs.lean](Codecs.lean) | Codec round trips, malformed input rejection, binary data, journal records, and an explicit broken-codec counterexample. |
| [Backends.lean](Backends.lean) | Immutable `StateT` storage over `Id`, mutable storage over `IO`, returned backend handles, state-dependent effect results, native exceptions, deep parallel nesting, and location navigation. |

Generated failures print both the seed and the program tree. The generator uses
fixed seeds, so the same test can be rerun with a prefix such as
`generated/seed/42`.

## Recovery boundaries

The checkpoint tests first obtain an uninterrupted baseline. For each journal
write in that run, they start again from an empty journal and inject an exception
immediately after that write commits. They discard the interrupted interpreter
call and restart using the retained backend state. The recovered outcome, effect
trace, backend state, and final journal must match the baseline. The workflows
include nested groups, blobs, typed failures, and an empty group.

Fuel tests repeat this comparison for initial budgets 0 through 79, then resume
with enough fuel to complete.

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

These tests exercise the current sequential replay driver and ideal in-memory
storage. They do not test concurrent workers, database adapters, cloud deployments,
or cancellation. Choice has only an explicit unsupported-operation check.

Equivalence assumes enough replay fuel, stable program/input, and codecs that
round-trip the values being persisted. The direct interpreter does not serialize
values, so a broken codec can make replay fail while direct execution succeeds;
the suite demonstrates that distinction. Passing the suite is evidence for the
implementation, not a formal equivalence proof.
