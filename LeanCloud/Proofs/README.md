# Interpreter equivalence proofs

Start with [MainTheorems.lean](MainTheorems.lean).

`sequential_replay_matches_direct` is the basic equivalence theorem:

> For the same pure program and input, sequential replay from empty storage
> returns exactly the direct interpreter's result, with sufficiently large fuel.

This theorem has no scheduler, mailbox, crash, fairness, or prefilled-cache
premise. [SequentialReplay.lean](../SequentialReplay.lean) drives the actual
`ReplayInterpreter.step`: execute each child in source order, then reconstruct
the parent from the original source and recorded results. The model is a pure
list of immutable records. Direct evaluation leaves that list untouched.
Both successes and application errors are covered, including nested and empty
parallel groups, delays, and delayed pure computations. Codecs must round-trip.

The proof constructs a finite execution and its sufficient fuel bound from the
pure source. [SequentialCursor.lean](SequentialCursor.lean) proves reconstruction,
[SequentialExecution.lean](SequentialExecution.lean) connects finite executions
to the fuel-based driver, and [SequentialReplay.lean](SequentialReplay.lean)
proves completion and the final result from empty storage. Its expected journal
is a proof witness, never runtime input.

The concurrent deployment adds scheduling and recovery:

`completed_replay_matches_direct` states:

> For a pure workflow, whenever the scheduler finishes, global storage contains
> a root result equal to direct evaluation of the same program and input.

`concurrent_replay_matches_direct` adds completion:

> For a pure workflow, there is a sufficient interpreter fuel bound. With at
> least that fuel and recurring timely processing windows, the scheduler
> eventually finishes and stores the direct interpreter's result.

Both concurrent theorems start with empty storage and the actual scheduler and worker
programs. The safety result covers any finite trace of their atomic operations, delayed replies,
independent crashes and restarts, late remote requests, message delivery,
duplication, and timer events. Neither theorem assumes that intermediate records,
assignments, reports, or scheduler states are correct: their correctness is proved.

The final `match` in the theorem makes existence explicit: missing storage is
`False`; a present record decodes to the direct interpreter's result. The result
can be success or a workflow error. There is no equality of external worlds.

[ProofExamples.lean](../../LeanCloudTests/ProofExamples.lean) applies all three theorems
to a workflow with nested parallel groups and captured values.
[ProgressWitness.lean](../../LeanCloudTests/ProgressWitness.lean) constructs a
concrete run of the actual actors from empty storage that satisfies the
processing-window assumption. Both are checked when building the test suite.

## Assumptions and limits

- `Pure.Evaluation` covers pure values, delay, failure, delayed pure computations,
  and parallel groups, including nested and empty groups. It describes the
  original Cloud program. Arbitrary IO actions, user blob effects, choice, and
  cancellation are outside this correctness theorem.
- Codecs preserve the values crossing replay boundaries. The root codec also
  round-trips so the final stored value can be decoded.
- The model has one scheduler with a private durable database. Its local writes
  are atomic; a pending local operation dies with its process. Workers cannot
  mutate that database.
- Global replay records support atomic create-if-absent and never change after
  creation. A remote request may commit after its actor crashes.
- Confirmed messages remain in durable transport until acknowledged. Delivery
  may be delayed or duplicated. Consumer sessions prevent stale receive/ack
  operations from affecting replacement sessions.

These are ideal service semantics. The theorem checks the existing interpreter
and actor code against Sim's ports. Real adapter and chaos tests provide evidence
for the implementations; they are not formal proofs of RabbitMQ, SQLite, or S3.

The safety theorem does not need fair scheduling or sufficient fuel: an
execution that never finishes still cannot publish a wrong pure result.

For eventual completion, [DeploymentProgress](DeploymentProgress.lean) makes the
extra assumption explicit. `Run` samples an actual execution after finite batches
of events. `MakesProgress` requires a later processing window whenever a sampled
state is unfinished. A window consists of:

1. A queued assignment executing the actual `Worker.execute` program to a report.
2. Its report reaching the scheduler while the attempt is still live.
3. A scheduler save applying that report's transition.

The window has actual deployment states and traces between them. Other actors,
broker delivery, and recovery may interleave between the worker's atomic
operations. [DeploymentExecution](DeploymentExecution.lean) connects each
operation and reply to those states; existing invariants prove that the worker's
contract survives the intervening events. No
successful report, root value, completed branch, or finished workflow is a
premise. `WorkerFuel.execute` proves the report succeeds with sufficient fuel.
`window_productive` then proves that saving it advances coordination. The finite
work bound rules out an unfinished run with infinitely many such windows.

This assumption is stronger than weak fairness and RabbitMQ durable delivery.
It excludes endless crashes, expiry before every report, and exhausted actor-loop
budgets that prevent further processing. It permits arbitrary finite failures
and delays between windows. Sampling boundaries must admit the required future
windows; this is a sufficient completion contract, not a characterization of
every schedule that happens to finish. RabbitMQ supplies message durability and
redelivery, not the execution and timely acceptance opportunities.

The following progress guarantees are checked:

- `ConcurrentSafety.unfinished_has_work`: every reachable unfinished scheduler
  has a pending or assigned job. Its unfinished jobs cannot all be waiting on
  one another.
- `SchedulerProgress.recovery_executes`: a healthy unfinished scheduler can
  issue an assignment on the next ready message after recovery.
- `WorkerProgress.job_can_report`: each job in a reachable scheduler state has
  a sufficient fuel bound and a finite uninterrupted execution of the actual
  worker that produces a fork or completion report. Completion already has a
  durable branch return. The bound includes replay of the recorded prefix; the
  caller supplies no continuation or expected journal.
- `WorkerFuel.execute`: the original pure source supplies one sufficient fuel
  bound for every worker, attempt, assignment, and compatible recorded snapshot.
  Finite possible locations and canonical typed replay prefixes give the bound.
- `SchedulerDelivery.completion_can_be_saved` and `fork_can_be_saved`: when a
  report is selected from the mailbox and its attempt is still live, one
  uninterrupted scheduler turn saves its completion or creates its child jobs,
  confirms the outgoing acknowledgement, then acknowledges the input. A root
  completion marks the workflow finished. Empty or already completed groups
  become runnable joins immediately. Stale reports preserve newer job progress.
- `ConcurrentSafety.completed_branch_persists` and `completion_persists`: once
  saved, branch and workflow completion survive every later actual actor,
  network, timeout, and recovery event. Completed jobs are never reopened or
  removed.
- `WorkerProgress.branch_keys_finite`: the pure source determines a finite set
  containing the return key of every reachable job, independent of worker count
  and scheduling. This bounds possible branch identities, not retry attempts.
- `ExecutionContracts.ForksAfter`: a worker cannot move backwards within its
  assigned branch. An authorized join cannot suspend again at its own fork.
  Worker execution proves this fact and mailbox transport preserves it for
  every report whose attempt remains live.
- `CoordinationProgress.productive_intervals_bounded`: the original pure source
  gives a finite bound on intervals that save live successful reports. A report
  can announce a fork or completion. Each such save strictly increases a bounded
  coordination measure; all other events preserve or increase it. The proof
  includes one job per branch, nested forks, empty groups, and retries.

These results construct possible sequences of commit/reply events for a worker
segment and a scheduler turn. `DeploymentProgress.eventually_finishes` combines
the source-wide fuel bound, finite coordination work, and the processing-window
assumption to prove completion. It does not claim completion under every schedule.

## Main proof path

| Files | What they establish |
| --- | --- |
| [Pure.lean](Pure.lean), [PureDirect.lean](PureDirect.lean) | Pure source meaning agrees with the actual direct interpreter. For SimM, direct evaluation is literally a pure value and issues no atomic requests. This does not assume syntactic monad associativity for lean-eff. |
| [Specification.lean](Specification.lean) | A finite expected journal exists for the pure workflow, including nested children and returns. It is a proof specification, not runtime input. |
| [Reconstruction.lean](Reconstruction.lean), [Resumption.lean](Resumption.lean), [Suspension.lean](Suspension.lean) | Recorded prefixes reconstruct the right typed continuations; each suspension supplies paths to its parent and children. |
| [ExecutionContracts.lean](ExecutionContracts.lean), [ResumptionContracts.lean](ResumptionContracts.lean), [WorkerContracts.lean](WorkerContracts.lean) | Actual worker execution, nested resumption, and reports preserve result correctness and reconstruction paths across interleaved store operations. Sufficient fuel excludes interpreter errors; workflow errors remain valid completions. |
| [SchedulerAssignments.lean](SchedulerAssignments.lean), [SchedulerRecords.lean](SchedulerRecords.lean), [SchedulerGroups.lean](SchedulerGroups.lean), [SchedulerPaths.lean](SchedulerPaths.lean) | Assignment identities, durable completion backing, child readiness, and reconstruction paths survive scheduler transitions and recovery. |
| [SchedulerProgress.lean](SchedulerProgress.lean) | Every waiting dependency has a job and points to a deeper branch; ready joins are awakened. These facts survive all scheduler transitions and recovery, ruling out a graph with only unfinished waiting jobs. |
| [SchedulerCompletion.lean](SchedulerCompletion.lean) | Completed jobs survive every scheduler transition and recovery. The shared actor guarantees carry this preservation through arbitrary concurrent traces. |
| [SchedulerRank.lean](SchedulerRank.lean), [CoordinationProgress.lean](CoordinationProgress.lean) | Branch uniqueness bounds job count. A source-dependent bounded measure increases on live successful report saves and never decreases across actual traces, bounding useful scheduling work. |
| [Mailbox.lean](Mailbox.lean), [Traffic.lean](Traffic.lean) | Durable transport preserves messages and their protocol certificates through delivery, duplication, acknowledgement, and disconnection. |
| [DeploymentContracts.lean](DeploymentContracts.lean), [SchedulerContracts.lean](SchedulerContracts.lean), [WorkerDeployment.lean](WorkerDeployment.lean) | Both actual actor startups and complete mailbox loops preserve the combined invariant. This includes scheduler save, outgoing publication, and incoming acknowledgement as separate operations. |
| [ConcurrentSafety.lean](ConcurrentSafety.lean) | Composes those actors through arbitrary actual Sim traces. `root_result` proves any published root value is correct; `completed_result` proves scheduler completion implies its durable presence. `trace_advances` retains completed jobs and records between any two reachable points. |
| [SimulationProgress.lean](SimulationProgress.lean), [WorkerProgress.lean](WorkerProgress.lean) | Realize an uninterrupted worker segment as actual commit/reply events, carrying its checked postcondition into the resulting report. Reachable job invariants supply the reconstruction path and fuel guarantee. |
| [SchedulerDelivery.lean](SchedulerDelivery.lean) | Realizes the actual scheduler turn, including private save, confirmed replies, and input acknowledgement. Live completion and fork reports become durable scheduler progress. |
| [WorkerFuel.lean](WorkerFuel.lean), [DeploymentProgress.lean](DeploymentProgress.lean) | Derive a source-wide fuel bound and eventual completion under recurring timely processing windows. Neither successful reports nor completion are supplied as premises. |
| [DeploymentExecution.lean](DeploymentExecution.lean) | Worker execution retains its contract with actual deployment events interleaved between atomic operations. The progress assumption does not require other actors to pause. |
| [MainTheorems.lean](MainTheorems.lean) | Connects that durable result to the actual direct interpreter on the same source and input. |

The composition uses [SimulationLogic.lean](SimulationLogic.lean): stable
assertions about requests and their saved continuations.
[SimulationSafety.lean](SimulationSafety.lean) and
[SimulationBackendSafety.lean](SimulationBackendSafety.lean) prove those assertions
sound for actual simulator events.
[SimulationRefinement.lean](SimulationRefinement.lean) reuses execution contracts
under the stronger deployment invariant; it checks the mutation guarantees rather
than duplicating the interpreter proof.

## Smaller results for review

- [CachedReplay.lean](CachedReplay.lean): `cached_replay_matches_direct` checks
  location-based replay against direct evaluation using the small pure journal
  in [ReplayModel.lean](ReplayModel.lean). Cached intermediate results and
  sufficient fuel are explicit premises. `resumed_branch_matches_direct` also
  covers reconstruction to a nested assignment. The public sequential theorem
  above removes the cache premise by executing and recording the children.
- [Parallel.lean](Parallel.lean), [ParallelContracts.lean](ParallelContracts.lean):
  joins preserve source order and the first error in that order, including empty
  groups. Actual interleaved reads retain the required child-record facts.
- [Segment.lean](Segment.lean), [Recording.lean](Recording.lean): a worker segment
  may create new records from empty compatible storage; it need not start with
  all intermediate results cached. Completion is stored before `done` is reported.
- [ReplayEvolution.lean](ReplayEvolution.lean),
  [RecordPreservation.lean](RecordPreservation.lean): committed records survive
  later execution, retries, and orphan writes. Create returns the canonical value.
- [WorkerOwnership.lean](WorkerOwnership.lean),
  [SchedulerOwnership.lean](SchedulerOwnership.lean): only the scheduler's own
  local commits can change its private database. These ownership results also
  support user effects that obey the stated access restrictions.
- [Recovery.lean](Recovery.lean), [Scheduler.lean](Scheduler.lean): recovery
  preserves progress, releases assignments, and is idempotent; stale reports do
  not complete newer attempts.
- [Location.lean](Location.lean), [JournalRegion.lean](JournalRegion.lean): location
  encodings are injective and separate command, return, sibling, and descendant
  record regions.

The old shared-queue and JournalDb proofs were retired with that implementation.
Git history retains them; they are not claims about this architecture.
