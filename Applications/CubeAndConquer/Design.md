# Depth-based parallel cube-and-conquer

The application takes an immutable DIMACS CNF file in blob storage and returns
a checked SAT model or an independently verifiable UNSAT bundle. See the
[workflow](CubeAndConquer/Workflow.lean) and [run instructions](README.md).

## Recursive cloud workflow

A branch is identified by its accumulated cube assumptions. Starting with the
empty cube, it either:

1. Runs Kissat and checks its certificate when the total depth is reached.
2. Runs `march_cu` for a bounded additional depth and creates a cloud branch for
   each child using `Cloud.parallel`.
3. Returns a checked SAT model, timeout, or error if march terminates early.

A cuber that produces the single empty extension has not split its input. That
branch goes to Kissat, including when march reports UNSAT: march's internal
refutation is not a certificate we accept.

```text
                         cube []
                       /         \
                  cube [x]      cube [-x]
                  /     \        /      \
              conquer conquer conquer conquer
                 +       +       +       +
               check   check   check   check
```

Each cubing action restores the original CNF and appends its parent assumptions
as unit clauses. Its output contains new decisions relative to that parent.
The workflow appends them to the parent's path before dispatching the children.
The pinned [march CLI](https://github.com/marijnheule/CnC#parameters) supports
DIMACS input, a static cutoff depth (`-d`), and cube output (`-o`). Independent
march processes provide distributed cubing; march does not coordinate the workers.

`depth` bounds total decisions along a path. `splitDepth` bounds new decisions
per march invocation; short paths retain their unused depth. Depth zero bypasses
march and goes directly to Kissat. A validated split must add at least one new
decision, so the recursive driver needs at most `depth` rounds.

A binary tree of depth `d` has at most `2^d` leaves. Request validation requires
that bound to fit `maxCubes`, keeping the safeguard independent of completion
order and avoiding shared counters. The actual tree can finish much earlier.

Sibling cubing actions run in parallel on available workers. The current runtime
scheduler finishes a batch and then visits its nested subtrees in order. The
application uses that existing behavior; it does not add another scheduler.
All branches finish before their parent combines results, even after SAT is found.

## Coverage and evidence

Before dispatch, validate that each split is a complete binary decision tree,
uses fresh variables relative to its parent, and stays within its depth budget.
Missing, duplicate, overlapping or over-depth leaves are errors.

The final worker publishes a flat leaf plan and evidence bundle. This keeps the
independent verifier simple: it checks complete coverage directly on accumulated
leaf assumptions, without trusting the intermediate cubing decisions or cloud
execution order. Cubes identify results; no separate global cube index is needed.

For SAT, check the model against the original CNF and the leaf's assumptions.
For UNSAT, require a checked DRAT proof for **every** leaf's original CNF plus
its accumulated unit clauses. Store each exact formula, proof, checker log and
solver diagnostics in blobs. The verification helper recreates the expected
formulas and reruns drat-trim. Unrelated per-leaf proofs are not concatenated
into a purported proof of the original formula.

The pinned [march output routine](https://github.com/marijnheule/CnC/blob/705b60c6491ef2b61988b3ce6ac674be1b90571d/march_cu/cube.c)
emits refuted leaves as well as open cubes. Retain and solve/check those leaves;
do not discard them based on an unverified cuber status.

Timeouts, UNKNOWN, malformed output and failed verification remain explicit
inconclusive/error leaf outcomes. A valid SAT witness can establish SAT despite
other inconclusive leaves. Otherwise, missing evidence cannot establish UNSAT.
These checks use external tools and application validation, not Lean kernel proofs.

## Durable actions and tooling

Cubing, solving, verification and final publication are separate `Cloud.exec`
actions. Each restores its immutable input into a private temporary workspace.
Only cube descriptions and artifact references enter the replay journal. A
recorded solver result can be reused if verification crashes, without rerunning
Kissat. Workers never depend on another worker's temporary files.

The application image contains pinned source builds of
[march_cu](https://github.com/marijnheule/CnC),
[Kissat](https://github.com/arminbiere/kissat), and
[drat-trim](https://github.com/marijnheule/drat-trim). Downloads are digest checked;
source revisions and executable digests are included in the result bundle.
Commands have deadlines and output limits; deployment-level memory/disk/CPU
quotas provide hard isolation. Credentials remain in deployment configuration.

Use larger `splitDepth` values to amortize repeated CNF loading and preprocessing.
Local caches and adaptive recubing of solver timeouts can be added after
measurement; neither is required by this workflow.

Tests cover generated formula oracles, direct/replay equivalence, every-write
recovery, uneven splits, depth bounds, real recursive cubing, certificate
corruption and a three-worker HTTP deployment. See the run instructions for
native and deployment test commands.
