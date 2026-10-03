# Interpreter equivalence

The main statements are in **[MainTheorems.lean](MainTheorems.lean)**.

| Theorem | Backend and execution model |
| --- | --- |
| `pure_replay_matches_direct` | Concrete pure Db and deterministic pending-work list; no fairness hypothesis. |
| `replay_matches_direct` | Exact Db map and lawful fair queue, with serialized worker steps. |
| `ConcurrentRecovery.concurrent_replay_matches_direct` | Shared atomic Db and leased-queue contracts, concurrent workers, delayed replies, crashes and replacement. |

All start with an empty Db and the root work item. They compare the returned
value or `CloudError` for the same program and input, and derive sufficient fuel.
The concurrent theorem also requires the same outcome in durable storage.

## Start with pure execution

[PureModel.lean](PureModel.lean) runs the existing interpreters over `Id`.
Replay uses a key/value journal, a list of pending locations and a completion
record. No IO, leases or external scheduler are involved.

```lean
import LeanCloud.Proofs.PureModel
open LeanCloud

def workflow (input : Nat) : Cloud Id Nat := do
  let values ← Cloud.parallel #[pure (input + 1), pure (input + 2)]
  return values.foldl (· + ·) 0

#eval Pure.direct workflow 10      -- .ok 23
#eval Pure.replay 100 workflow 10  -- .ok 23

def saved := (Pure.resume 1 workflow 10 Pure.initial).2
#eval saved.pending.map Location.key -- ["0:0/0:0", "0:0/1:0"]
#eval (Pure.resume 100 workflow 10 saved).1 -- .ok 23
```

The supporting [PureReplay.lean](PureReplay.lean) theorem also covers resuming a
valid partial execution. Its validity premise requires the saved records and
pending locations to agree with the program; arbitrary fabricated records do
not satisfy it.

## The concurrent guarantee

Read `concurrent_replay_matches_direct` as:

```text
The workflow determines a traversal bound and an expected outcome.
Direct evaluation returns that expected outcome without service operations.

For every fair concurrent execution and each worker:
  there is a completing prefix after crashes stop;
  every per-worker fuel assignment above traversal + prefix length
  realizes that prefix with the public replay interpreter;
  the worker returns expected, with its lease receipt cleared;
  the durable completion record contains the encoding of expected.
```

`expected` is chosen before the schedule. Branch order, retries and crashes
cannot change it. The completing prefix and fuel bound may depend on the
schedule. No fixed fuel budget covers all fair schedules, since fairness does
not impose a maximum delay.

For a workflow computing `input + 1` and `2 * input` in parallel, input `10`
gives `.ok (11, 20)`, even if the second branch finishes first. Workflow failure
is also covered, including the direct interpreter's array-order error priority.

Three definitions make the statement readable:

- [RecordedComparisons](BackendEquivalence.lean) requires equality tests to
  recognize the workflow's recorded JSON values and exits. This is a
  serialization requirement.
- `FairExecution`, in the main file, requires initialization at the root, fair
  worker actions and delivery, and eventual cessation of crashes. It assumes
  neither successful processing nor completion.
- `ReplayMatches`, in the main file, contains an actual finite execution witness
  using exactly the supplied public-interpreter fuel. It requires the returned
  outcome, durable encoding, cleared receipt and matching shared service state.

The witness preserves every physical commit, reply, crash and restart. Idle time
and administrative iteration boundaries stutter. Private request ids may be
renamed: the real loop can issue its next request earlier than the repeated
proof model. Corresponding requests keep their operation, reply and worker
identity. This prevents replacing the given execution with a convenient schedule.

[concurrent_output_safety](BackendEquivalence.lean) separately covers arbitrary
fuel and legal scheduling without fairness. A returned result is the expected
outcome or fuel exhaustion; every stored completion is the expected encoding.
The main theorem derives completion and enough fuel to obtain exact equality.

## Contracts and scope

The [shared backend contracts](../Backend.md) describe individually atomic Db
reads and compatible writes, durable publication, receipt-based delivery and
acknowledgement. The queue can reorder work, duplicate delivery after an
acknowledgement, and accept stale receipts. Calls issued by a crashed worker can
commit later, without resuming its replacement.

Fairness requires continuously enabled live commits, replies and replacements
to progress. Unfinished iterations repeat fairly. While consumers keep polling,
unacknowledged publications are eventually selected or acknowledged. Continued
polling and successful processing are proved from the interpreter. After some
finite point, crashes stop. Orphaned requests need not reply or commit, and have
no maximum permitted delay.

The supported fragment is ordinary `pure`/`return`, bind, `delay`, `fail` and
`parallel`, including nested and empty groups. [PureProgram](Assumptions.lean)
checks continuations for all possible arguments. Final and parallel codecs must
decode their own encodings. `RecordedComparisons` states the needed reflexivity
because Lean does not provide a general `LawfulBEq Json` instance.

Exec/IO, user blob effects, cancellation, choice and the recorded `Cloud.pure`
helper are outside this theorem. The direct interpreter uses no backend state
for the supported fragment. There is no external user-world equality premise.

Provider implementations are assessed against the same primitive contracts.
Finite conformance and differential tests provide evidence, not a proof of an
external service or infinite fairness. The theorem assumes durable data survives
and replacements use the same program and input.

## Reading the proof

1. [Evaluation](Evaluation.lean) and [ExecutionTree](ExecutionTree.lean) give the
   pure program its finite meaning and permitted records.
2. [BackendSafety](BackendSafety.lean) composes primitive contracts across
   interleaved commits, delayed replies and orphaned requests.
   [BackendJournal](BackendJournal.lean), [BackendRead](BackendRead.lean) and
   [BackendStep](BackendStep.lean) prove the actual location-based replay step.
3. [BackendHandoff](BackendHandoff.lean) proves publication before acknowledgement.
   [BackendAccounting](BackendAccounting.lean) proves no loss of unfinished work.
   [BackendAccountedLoop](BackendAccountedLoop.lean) carries this through the
   actual finite worker loop.
4. [BackendPolling](BackendPolling.lean) derives continued consumer demand.
   [BackendDelivery](BackendDelivery.lean) follows a selected request's actual
   continuation through successful publication. [BackendOrphans](BackendOrphans.lean)
   accounts for requests left behind by crashed generations.
5. [BackendTermination](BackendTermination.lean) combines finite journal
   stabilization, decreasing work rank and fair delivery to prove durable
   completion. [BackendReturns](BackendReturns.lean) proves each worker observes it.
6. [BackendFuelProgram](BackendFuelProgram.lean), [BackendFuelTrace](BackendFuelTrace.lean)
   and [BackendRealization](BackendRealization.lean) realize that finite prefix
   with the unchanged public fuel-based interpreter.

[ReplayIteration.iteration](ReplayIteration.lean) is a factoring of one actual
poll/process/publish iteration, not another runtime interpreter. The older
`Concurrent*.lean` files retain the narrower `SimM` proofs and shared structural
lemmas; the main concurrent theorem now uses the `Backend*.lean` contract proofs.

## Verification

Run `lake build` and `lake test`. To audit the main dependencies:

```lean
import LeanCloud.Proofs.MainTheorems

#print axioms LeanCloud.Proofs.pure_replay_matches_direct
#print axioms LeanCloud.Proofs.replay_matches_direct
#print axioms LeanCloud.Proofs.ConcurrentRecovery.concurrent_replay_matches_direct
#print axioms LeanCloud.Backend.Proofs.concurrent_output_safety
```

The main theorems use only Lean's standard `propext`, `Classical.choice` and
`Quot.sound` axioms. There are no proof holes or custom correctness axioms;
codec, comparison and environment requirements are explicit hypotheses.
