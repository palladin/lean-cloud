import LeanCloudTests.Support
import LeanCloudTests.StressWorkload
import LeanCloud.ParallelReplay
import LeanCloud.RestartingParallelReplay

namespace LeanCloudTests.Stress
open Lean LeanCloud StressWorkload

private def timed (action : Unit → α) : IO (α × Nat) := do
  -- Reading the thunk after the clock and storing its result before the next
  -- clock prevent the compiler from hoisting a pure evaluation out of the span.
  let thunk ← IO.mkRef action
  let start ← IO.monoMsNow
  let action ← thunk.get
  let result ← IO.mkRef (action ())
  let elapsed := (← IO.monoMsNow) - start
  return (← result.get, elapsed)

private def sameJournal (expected actual : ReplayModel.Journal) : IO Unit := do
  assertEq actual.length expected.length "Record count differs"
  for (key, record) in expected do
    assertEq (actual.lookup key) (some record) s!"Missing or changed record: {key}"

/-- Report observations without treating machine-dependent timings as laws.
Each branch loses a read response and a committed return response in recovery. -/
def measure (input : Input) : IO Json := do
  let fuel := 100000
  let ((expected, untouched), directMs) ← timed fun _ =>
    (DirectInterpreter.interpret ReplayModel.noBlobs workflow input).run []
  assertTrue untouched.isEmpty "Direct evaluation used the journal"
  let ((sequential, journal), sequentialMs) ← timed fun _ =>
    (SequentialReplay.interpret ReplayModel.store ReplayModel.noBlobs fuel workflow input).run []
  assertOutcome sequential expected
  let ((parallel, merged), parallelMs) ← timed fun _ =>
    (ParallelReplay.interpret fuel workflow input).run []
  assertOutcome parallel expected
  sameJournal journal merged
  let ((clean, baseline), cleanMs) ← timed fun _ =>
    (RestartingParallelReplay.interpret fuel workflow input).run (ReplayFaults.Saved.initial {})
  assertOutcome clean expected
  sameJournal journal baseline.journal
  let plan : ReplayFaults.Plan := { workers := baseline.workers.map fun (branch, _) =>
    (branch, [⟨.read (ReplayStore.returnKey branch), .before⟩,
      ⟨.create (ReplayStore.returnKey branch), .after⟩]) }
  let ((recovered, saved), recoveryMs) ← timed fun _ =>
    (RestartingParallelReplay.interpret fuel workflow input).run (ReplayFaults.Saved.initial plan)
  assertOutcome recovered expected
  sameJournal journal saved.journal
  let crashes := saved.workers.foldl (fun n (_, faults) => n + faults.crashes) 0
  assertEq crashes (plan.workers.length * 2) "Fault plan was not exercised"
  assertTrue (saved.workers.all fun (_, faults) => faults.remaining.isEmpty) "Unconsumed faults"
  let ((warm, unchanged), warmMs) ← timed fun _ =>
    (RestartingParallelReplay.interpret 1 workflow input).run saved
  assertOutcome warm expected
  assertEq unchanged.journal saved.journal "Warm replay changed durable records"
  let calls := baseline.workers.flatMap (fun (_, faults) => faults.visited.toList)
  let recoveryCalls := saved.workers.flatMap (fun (_, faults) => faults.visited.toList)
  let reads := fun calls => (calls.filter fun op => match op with | ReplayFaults.Operation.read _ => true | _ => false).length
  return Json.mkObj [
    ("input", toJson input), ("records", toJson journal.length),
    ("branches", toJson baseline.workers.length), ("reads", toJson (reads calls)),
    ("creates", toJson (calls.length - reads calls)), ("crashes", toJson crashes),
    ("recoveryReads", toJson (reads recoveryCalls)),
    ("recoveryCreates", toJson (recoveryCalls.length - reads recoveryCalls)),
    ("directMs", toJson directMs), ("sequentialMs", toJson sequentialMs),
    ("parallelMs", toJson parallelMs), ("cleanWorkerMs", toJson cleanMs),
    ("recoveryMs", toJson recoveryMs), ("warmMs", toJson warmMs)]

def cases : Array TestCase := smoke.map fun input =>
  ⟨s!"stress/{reprStr input.shape}/{input.size}", do discard (measure input)⟩

end LeanCloudTests.Stress
