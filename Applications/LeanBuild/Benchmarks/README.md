# Offline scheduler benchmark

Compare LeanBuild's planner with open-source
[MiniZinc](https://github.com/MiniZinc/libminizinc) (MPL 2.0) and
[OR-Tools CP-SAT](https://github.com/google/or-tools) (Apache 2.0).
This optional executable is separate from `cloud_app`: it neither builds Mathlib
nor provisions infrastructure, and it does not replace the production planner.

## Model and validation

Each module costs one CPU time unit. A `(round, worker)` pair is a job.
Dependencies must finish first; a dependency in the same round must belong to
the same job. Worker capacities limit simultaneous modules. Rounds have barriers.

`schedule.mzn` chooses starts, worker assignments and rounds. Its objective is:

```text
compute span + overhead per round × number of rounds
```

The overhead is an explicit modeling assumption, not a measured transfer time.
Zero minimizes compute alone. The recorded experiment uses one unit per round.
The heuristic supplies a feasible incumbent and an objective upper bound.
CPU-work and dependency-path bounds narrow the search without excluding better
solutions within the requested round bound. For example, 9,031 modules on 28
CPUs need at least 323 units; a cost bound of 359 with overhead 1 allows at most
36 rounds, even when the caller requests a bound of 58.

`barriers.mzn` is a separate, restricted experiment: it fixes the incumbent's
module start times and minimizes rounds by changing worker assignments and cut
positions. Optimality here applies only to those fixed times.

Lean independently checks every returned solution's coverage, dependencies,
worker capacity and round boundaries. It then runs the returned grouping through
the same critical-order list scheduling policy used to score the heuristic.
The report separates solver timings from re-simulated timings: Lake does not
promise to follow the optimizer's starts. `bestValidated` includes the incumbent
fallback; an empty `candidates` array means the solver returned no schedule.
An `OPTIMAL_SOLUTION` status is the solver's conclusion, not a Lean proof of
optimality. The Lean checker validates feasibility, not the solver's lower bound.

The model excludes unequal compilation costs, memory pressure, artifact sizes,
network contention, failures and final target linking. Worker IDs denote planning
slots; the runtime does not currently enforce placement on those particular
workers. The Mathlib experiment uses homogeneous capacities. These results are
not a cloud build speedup or a guarantee about real CPU utilization.

## Run

Install a MiniZinc bundle with the open-source `cp-sat` backend. The experiment
used MiniZinc 2.10.1 and CP-SAT 9.15 on macOS ARM64. Set `MINIZINC` if its binary
is not on `PATH`; no Python or proprietary solver is used.

From `Applications/LeanBuild`:

```sh
lake build plan_bench
./Benchmarks/test.sh /tmp/lean-build-solver-tests

# DAG.json is the prepared, topologically ordered array of {name, imports}.
# Arguments after OUT: CPU capacities, overhead per round, maximum rounds.
.lake/build/bin/plan_bench prepare /path/to/DAG.json /tmp/mathlib-plan 7,7,7,7 1 58

# Arguments: model, case directory, total time budget in ms, solver threads.
./Benchmarks/solve.sh schedule /tmp/mathlib-plan 180000 4
./Benchmarks/solve.sh barriers /tmp/mathlib-plan 60000 4

# Optimize just baseline rounds 2–3, retaining global module priority.
.lake/build/bin/plan_bench window /tmp/mathlib-plan /tmp/mathlib-window 2 3
./Benchmarks/solve.sh schedule /tmp/mathlib-window 5000 1
```

`case.json` keeps the graph, capacities and exact incumbent. `instance.json` is
the solver input. Each solve saves JSON messages, timing and a validated report
in that directory. A time limit can end with a feasible incumbent without an
optimality status, or with `UNKNOWN` and no candidate. Setup and shutdown can add
a little wall time beyond the requested budget.

For a reproducible sweep of all adjacent pairs, use the baseline round count:

```sh
rounds=$(jq -r '.metrics.rounds' /tmp/mathlib-plan/case.json)
for ((first=1; first<rounds; first++)); do
  out="/tmp/mathlib-pair-$first"
  .lake/build/bin/plan_bench window /tmp/mathlib-plan "$out" "$first" "$((first+1))"
  ./Benchmarks/solve.sh schedule "$out" 5000 1
done
```

## Mathlib result, 2026-10-24

Machine-readable measurements are in [mathlib-result.json](mathlib-result.json).

Input: 9,031 modules and 32,949 dependency edges, from Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, target `Mathlib`.
The saved DAG's SHA-256 is
`1663b2136485e9b6a719b273f4d99886db2f301d9a3f9e76ccc844bd87325792`.

| Experiment | Result |
| --- | --- |
| Current heuristic | 29 rounds, 113 jobs, 330 compute units; about 0.8 s planning and simulation |
| Full scheduling search | No candidate within a three-minute budget (181.5 s wall time) |
| Fixed-start barrier search | 29 rounds is optimal for those starts; same validated plan metrics, about 16.5 s |
| All 28 adjacent pairs, 5 s each | No improvement; 10 local optima reported, 16 feasible without proof, 2 without a candidate; about 94 s total |

Keep the current heuristic. This formulation did not justify adding a solver
to the runtime. The restricted result supports its barrier choices, while the
full timeout leaves global optimality unresolved. A different formulation or
measured compilation costs could change the comparison.
