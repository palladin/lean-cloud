import LeanCloudTests.Support
import LeanCloud.RestartingParallelReplay

namespace LeanCloudTests.RestartingReplay
open Lean LeanCloud ReplayFaults
open RestartingParallelReplay (interpret)

private def crashes (saved : Saved) : Nat :=
  saved.workers.foldl (fun total (_, faults) => total + faults.crashes) 0

private def differential [Codec α] [BEq α] [Repr α]
    (program : ι → Cloud WorkerM α) (input : ι) (plan : Plan := {}) : IO Saved := do
  let (.ok expected, untouched) := ((DirectInterpreter.interpret noBlobs program input).run).run ⟨[], {}⟩
    | throw (IO.userError "Direct interpreter was interrupted")
  assertTrue (untouched.durable.isEmpty && untouched.faults.visited.isEmpty) "Direct used replay storage"
  let (.ok clean, sequential) :=
    ((SequentialReplay.interpret store noBlobs 10000 program input).run).run ⟨[], {}⟩
    | throw (IO.userError "Unfaulted sequential replay was interrupted")
  assertOutcome clean expected
  let (actual, saved) := (interpret 10000 program input).run (Saved.initial plan)
  assertOutcome actual expected
  assertEq saved.journal.length sequential.durable.length "Recovery duplicated or lost durable records"
  for (key, record) in sequential.durable do
    assertEq (saved.journal.lookup key) (some record) s!"Recovery changed {key}"
  let some root := saved.journal.lookup (ReplayStore.returnKey Location.root)
    | throw (IO.userError "Recovery returned without a durable root result")
  assertOutcome (ReplayInterpreter.result (m := Id) root.outcome).run expected
  for (branch, faults) in saved.workers do
    assertTrue faults.remaining.isEmpty s!"Unexercised worker faults at {branch.key}: {reprStr faults.remaining}"
  let (warm, unchanged) := (interpret 1 program input).run saved
  assertOutcome warm expected
  assertEq unchanged.journal saved.journal "Warm replay wrote new records"
  return saved

private def nested [Pure m] (input : Nat) : Cloud m Nat := do
  let captured ← Cloud.pure (fun _ => input * 2) "capture"
  let values ← Cloud.parallel #[
    (do
      let value ← Cloud.pure (fun _ => captured + 1) "first"
      let inner ← Cloud.parallel #[pure value, Cloud.delay fun _ => pure (value + 1)]
      return inner.foldl (· + ·) 0),
    Cloud.delay fun _ => Cloud.pure (fun _ => captured + 3) "second"]
  let later ← Cloud.parallel #[pure values.size, pure input]
  Cloud.pure (fun _ => values.foldl (· + ·) 0 + later.foldl (· + ·) 0) "result"

private def pair (_ : Unit) : Cloud WorkerM (Array Nat) :=
  Cloud.parallel #[Cloud.pure (fun _ => 7), Cloud.pure (fun _ => 9)]

private def pureTree : Tree → Tree
  | .blob n => .effect n
  | .delay child => .delay (pureTree child)
  | .bind first next => .bind (pureTree first) (pureTree next)
  | .branch even odd => .branch (pureTree even) (pureTree odd)
  | .parallel children => .parallel (children.map pureTree)
  | tree => tree

private def faultsFor (seed : Nat) (calls : Array ReplayFaults.Operation) : List Fault :=
  (calls[seed % max 1 calls.size]?).toList.map fun operation =>
    ⟨operation, if seed % 2 == 0 then .before else .after⟩

def cases : Array TestCase := #[
  ⟨"restarting-replay/storage-before-and-after-commit", do
    let key := ReplayStore.valueKey Location.root
    let record : ReplayRecord := ⟨⟨"exec", "nat", .null⟩, .success (toJson (7 : Nat))⟩
    for side in [Side.before, .after] do
      let (outcome, saved) := (store.create key record).run
        { durable := [], faults.remaining := [⟨.create key, side⟩] }
      match outcome with
      | .error actual => assertEq actual side
      | .ok _ => throw (IO.userError "Storage fault did not interrupt")
      assertEq (saved.durable.lookup key) (if side == .before then none else some record)
      let replacement := { record with outcome := .success (toJson (99 : Nat)) }
      let (.ok accepted, retried) := (store.create key replacement).run saved
        | throw (IO.userError "Consumed fault fired again")
      assertEq accepted (if side == .before then replacement else record)
      assertEq retried.durable.length 1 "Retry duplicated a committed key"⟩,
  ⟨"restarting-replay/worker-retry-stays-inside-spawn", do
    let branch := Location.root.child 0
    let key := ReplayStore.valueKey branch
    let saved ← differential pair () { workers := [(branch, [⟨.create key, .after⟩])] }
    assertEq (crashes saved) 1
    let worker := (saved.workers.lookup branch).getD {}
    assertEq (worker.visited.filter (· == .create key)).size 1 "Worker repeated a committed computation"
    let sibling := (saved.workers.lookup (Location.root.child 1)).getD {}
    assertEq (sibling.visited.filter (· == .read (ReplayStore.returnKey (Location.root.child 1)))).size 2
      "Worker crash restarted its sibling"⟩,
  ⟨"restarting-replay/completed-worker-returns-the-recorded-outcome", do
    let program (_ : Unit) : Cloud WorkerM Nat := Cloud.pure (fun _ => 7)
    let key := ReplayStore.returnKey Location.root
    let saved : State ReplayModel.Journal := {
      durable := [], faults.remaining := [⟨.create key, .after⟩] }
    let (result, finished) := (worker 2 20 program () ⟨0, Location.root⟩).run saved
    assertOutcome result (.ok (.done (.success (toJson (7 : Nat)))))
    assertEq finished.faults.crashes 1
    assertEq (finished.faults.visited.filter (· == .create key)).size 1
      "Lost reply caused a second terminal write"
    let some record := finished.durable.lookup key | throw (IO.userError "Missing worker return")
    assertOutcome result (.ok (.done record.outcome))⟩,
  ⟨"restarting-replay/suspension-retries-return-the-same-report", do
    let program (_ : Unit) : Cloud WorkerM (Array Nat) := do
      let n ← Cloud.pure (fun _ => 7)
      Cloud.parallel #[pure n, pure (n + 1)]
    let assignment : Assignment := ⟨0, Location.root⟩
    let (expected, clean) := (worker 1 20 program () assignment).run ⟨[], {}⟩
    assertOutcome expected (.ok (.fork Location.root.next 2))
    for operation in clean.faults.visited.toList.eraseDups do
      for side in [Side.before, .after] do
        let initial : State ReplayModel.Journal := { durable := [], faults.remaining := [⟨operation, side⟩] }
        let (actual, recovered) := (worker 2 20 program () assignment).run initial
        assertOutcome actual expected
        assertEq recovered.durable clean.durable "Local retry changed the suspension journal"
        assertEq recovered.faults.crashes 1⟩,
  ⟨"restarting-replay/interpreter-budget-errors-are-not-crashes", do
    let program (_ : Unit) : Cloud WorkerM Nat := pure 7
    let (result, saved) := (worker 100 0 program () ⟨0, Location.root⟩).run ⟨[], {}⟩
    assertError result .protocol
    assertEq saved.faults.crashes 0
    assertEq saved.faults.visited.size 1 "Interpreter budget exhaustion was retried"⟩,
  ⟨"restarting-replay/exhausted-worker-keeps-completed-siblings", do
    let branch := Location.root.child 0
    let faults := List.replicate 20 ⟨.read (ReplayStore.returnKey branch), Side.before⟩
    let (result, saved) := (interpret 10 pair ()).run (Saved.initial { workers := [(branch, faults)] })
    assertError result .protocol
    let sibling := Location.root.child 1
    assertTrue (saved.journal.lookup (ReplayStore.returnKey sibling)).isSome
      "Worker exhaustion discarded a completed sibling"
    assertTrue (saved.journal.lookup (ReplayStore.returnKey Location.root)).isNone
      "Unfinished root was marked complete"
    let (result, resumed) := (interpret 100 pair ()).run saved
    assertOutcome result (.ok #[7, 9])
    let history := (resumed.workers.lookup sibling).getD {}
    assertEq (history.visited.filter (· == .create (ReplayStore.returnKey sibling))).size 1⟩,
  ⟨"restarting-replay/repeated-crashes-and-fuel-resumption", do
    let program (_ : Unit) : Cloud WorkerM Nat := pure 7
    let faults := List.replicate 3 ⟨.read (ReplayStore.returnKey Location.root), Side.before⟩
    let (outcome, saved) := (interpret 2 program ()).run (Saved.initial { workers := [(Location.root, faults)] })
    assertError outcome .protocol
    assertEq (crashes saved) 2
    assertTrue saved.journal.isEmpty "Interrupted worker wrote a terminal result"
    let (outcome, saved) := (interpret 100 program ()).run saved
    assertOutcome outcome (.ok 7)
    assertEq (crashes saved) 3
    assertTrue ((saved.workers.lookup Location.root).getD {}).remaining.isEmpty "Fault script was reset"⟩,
  ⟨"restarting-replay/application-failures-stay-in-source-order", do
    let program (_ : Unit) : Cloud WorkerM (Array Nat) :=
      Cloud.parallel #[Cloud.fail "first", Cloud.delay fun _ => Cloud.fail "second", Cloud.pure (fun _ => 42)]
    let branches := (List.range 3).map Location.root.child
    let saved ← differential program () {
      workers := [(Location.root.child 0, [⟨.create (ReplayStore.returnKey (Location.root.child 0)), .after⟩])] }
    assertEq (crashes saved) 1
    for branch in branches do
      assertTrue (saved.journal.lookup (ReplayStore.returnKey branch)).isSome "Failure discarded a sibling"
    let some root := saved.journal.lookup (ReplayStore.returnKey Location.root)
      | throw (IO.userError "Missing failure")
    assertEq root.outcome (.failure ⟨.application, "first"⟩)⟩,
  ⟨"restarting-replay/empty-group-and-lost-return-reply", do
    let program (_ : Unit) : Cloud WorkerM (Array Nat) := Cloud.parallel #[]
    let saved ← differential program () { workers := [(Location.root,
      [⟨.create (ReplayStore.valueKey Location.root), .after⟩,
       ⟨.create (ReplayStore.returnKey Location.root), .after⟩])] }
    assertEq (crashes saved) 2
    assertEq saved.workers.length 1 "Empty group spawned child workers"⟩,
  ⟨"restarting-replay/overlapping-worker-writes-are-invalid", do
    let branch := Location.root.child 0
    let assignments : List Assignment := [⟨0, branch⟩, ⟨0, branch⟩]
    let (result, saved) := (workers (pair ()) 100 assignments).run (Saved.initial {})
    assertError result .divergence
    assertTrue saved.journal.isEmpty "Invalid union partially changed the journal"⟩,
  ⟨"restarting-replay/every-nested-boundary-before-and-after", do
    let clean ← differential nested 7
    for (branch, faults) in clean.workers do
      for operation in faults.visited.toList.eraseDups do
        for side in [Side.before, .after] do
          let plan : Plan := { workers := [(branch, [⟨operation, side⟩])] }
          try
            let saved ← differential nested 7 plan
            assertEq (crashes saved) 1
          catch error =>
            throw (IO.userError s!"worker={branch.key}, {reprStr operation}, {reprStr side}: {error}")⟩
] ++ (Array.range 128).map fun seed =>
  ⟨s!"restarting-replay/generated/{seed}", do
    let tree := pureTree (generate (3 + seed % 3) seed).1
    let program := lower tree (m := WorkerM)
    try
      let clean ← differential program (seed % 17)
      let plan : Plan := {
        workers := clean.workers.zipIdx.map fun ((branch, faults), index) =>
          (branch, faultsFor (seed + index) faults.visited) }
      let recovered ← differential program (seed % 17) plan
      let planned := plan.workers.foldl (fun n (_, faults) => n + faults.length) 0
      assertEq (crashes recovered) planned
    catch error => throw (IO.userError s!"seed={seed}, program={reprStr tree}\n{error}")⟩

end LeanCloudTests.RestartingReplay
