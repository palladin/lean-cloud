import LeanCloudTests.Generated

namespace LeanCloudTests.Crashes
open Lean LeanCloud
open LeanCloud.Proofs

abbrev M := CrashModel.M ReplayModel.State
abbrev State := CrashModel.State ReplayModel.State

/-- Reuse the proof model's exact Db; only the primitive boundaries can crash. -/
def db : Db Unit M where
  get key handle := do
    return (← CrashModel.atomic (ReplayModel.db.get key), handle)
  put key value handle := do
    return (← CrashModel.atomic (ReplayModel.db.put key value), handle)

def noBlobs : BlobStorage Unit M where
  putBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
  readBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
  resolveBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩

/-- Selection retains the item. Publication remains one atomic operation here;
leases and separate enqueue/ack boundaries are not part of this model yet. -/
def queue (reverse : Bool) : WorkQueue Unit M where
  next handle := do
    let work ← CrashModel.atomic fun state =>
      let work := match state.completed with
        | some outcome => Work.completed outcome
        | none =>
          let pending := if reverse then state.pending.reverse else state.pending
          match pending.head? with
          | some location => .item location
          | none => .idle
      (work, state)
    return (work, handle)
  complete location update handle := do
    let _ ← CrashModel.atomic fun state => ((), ReplayModel.update state location update)
    return ((), handle)

def attempt [Codec α] (program : Nat → Cloud M α) (input : Nat)
    (reverse : Bool := false) (fuel : Nat := 10000) : M (Except CloudError α) :=
  Prod.fst <$> (interpret db noBlobs (queue reverse) fuel program input).run ()

def initial : State := ⟨ReplayModel.initial, {}⟩

def outcome (result : Except Crash (Except CloudError α)) : IO (Except CloudError α) :=
  match result with
  | .ok result => pure result
  | .error _ => throw (IO.userError "Unexpected unrecovered crash")

def nested {m : Type → Type} (input : Nat) : Cloud m Nat := cloud {
  let values ← Cloud.parallel #[cloud {
    let children ← Cloud.parallel #[pure input, pure (input + 1)]
    return children.foldl (· + ·) 0
  }, cloud {
    let empty ← Cloud.parallel (#[] : Array (Cloud m Nat))
    return input + empty.size
  }, pure (input * 2)]
  let (left, right) ← cloud { return values.foldl (· + ·) 0 } || cloud { return input + 3 }
  return left + right
}

/-- Compare with structural direct evaluation after interrupting every primitive
of an uninterrupted run. Also discard the attempt explicitly and resume under
the opposite queue policy, using the state left at the exact crash boundary. -/
def sweep [Codec α] [BEq α] [Repr α]
    (program : Nat → Cloud M α) (directProgram : Nat → Cloud Id α) : IO Unit := do
  let input := 7
  let (expected, _) :=
    (DirectInterpreter.interpret (Proofs.noBlobs : BlobStorage Unit Id) directProgram input).run ()
  for reverse in [false, true] do
    let action := attempt program input reverse
    let (baseline, finished) := (CrashM.restart 0 action).run initial
    assertOutcome (← outcome baseline) expected
    assertTrue finished.durable.completed.isSome "Missing durable completion"
    for boundary in [CrashModel.Boundary.before, .after] do
      for cut in [:finished.faults.calls] do
        let start : State := { initial with faults.script := List.replicate cut none ++ [some boundary] }
        let (crashed, interrupted) := (CrashM.restart 0 action).run start
        assertTrue (match crashed with | .error .stopped => true | _ => false)
          s!"Crash not reached: call={cut}, boundary={reprStr boundary}"
        assertEq interrupted.faults.calls (cut + 1)
        let (resumed, recovered) :=
          (CrashM.restart 0 (attempt program input (!reverse))).run interrupted
        assertOutcome (← outcome resumed) expected
        assertEq recovered.durable.pending [] "Recovered queue retained work"
        assertEq recovered.durable.completed finished.durable.completed
        let (automatic, _) := (CrashM.restart 1 action).run start
        assertOutcome (← outcome automatic) expected

mutual
  /-- Instantiate the same pure workflow definition in Id and the crash monad.
  Generated effect/blob leaves become ordinary values in this pure-only suite. -/
  def lowerPure {m : Type → Type} (tree : Tree) (input : Nat) : Cloud m Nat :=
    match tree with
    | .value n | .effect n | .blob n => pure (input + n)
    | .fail n => Cloud.fail s!"generated-failure/{n}"
    | .delay child => Cloud.delay fun _ => lowerPure child input
    | .bind first next => do
      let value ← lowerPure first input
      lowerPure next (value + input)
    | .branch even odd =>
      if input % 2 == 0 then lowerPure even input else lowerPure odd input
    | .parallel children => do
      let values ← Cloud.parallel (lowerPureChildren children input).toArray
      return values.foldl (· + ·) input
  termination_by structural tree

  def lowerPureChildren {m : Type → Type} (children : List Tree) (input : Nat) :
      List (Cloud m Nat) :=
    match children with
    | [] => []
    | child :: rest => lowerPure child input :: lowerPureChildren rest input
  termination_by structural children
end

def cases : Array TestCase := #[
  ⟨"crash/sweep/nested", sweep nested nested⟩,
  ⟨"crash/sweep/value", sweep (fun n => pure n) (fun n => pure n)⟩,
  ⟨"crash/sweep/failure", sweep
    (fun _ => Cloud.fail "expected" : Nat → Cloud M Nat)
    (fun _ => Cloud.fail "expected")⟩,
  ⟨"crash/sweep/empty", sweep
    (fun _ => Cloud.parallel (#[] : Array (Cloud M Nat)))
    (fun _ => Cloud.parallel (#[] : Array (Cloud Id Nat)))⟩,
  ⟨"crash/cloud-error-is-not-retried", do
    let error : CloudError := ⟨.application, "expected"⟩
    let action : CrashM Nat (Except CloudError Nat) := fun count => (.ok (.error error), count + 1)
    let (result, count) := (CrashM.restart 20 action).run 0
    assertOutcome (← outcome result) (.error error)
    assertEq count 1⟩,
  ⟨"crash/bypasses-interpreter-catch", do
    let program (_ : Nat) : Cloud M Nat := Cloud.exec (fun _ => throw Crash.stopped)
    let (result, state) := (attempt program 0).run initial
    assertTrue (match result with | .error .stopped => true | _ => false)
      "Crash was caught as a CloudError"
    assertEq (state.durable.journal Location.root.key) none "Crash was journaled as a workflow failure"
    assertEq state.durable.pending [Location.root]
    assertEq state.durable.completed none⟩,
  ⟨"crash/fresh-worker-local-state", do
    let action : StateT Nat (CrashM Nat) Nat := do
      modify (· + 1)
      let interrupt : CrashM Nat Unit := fun count =>
        (if count == 0 then .error .stopped else .ok (), count + 1)
      liftM interrupt
      get
    let (result, durable) := (CrashM.restart 1 (action 0)).run 0
    match result with
    | .ok values => assertEq values (1, 1) "Worker-local state leaked across attempts"
    | .error _ => throw (IO.userError "Fresh worker did not recover")
    assertEq durable 2 "Durable state was rolled back"⟩,
  ⟨"crash/repeated-interruption", do
    let script := (List.range 24).map (fun i => some (if i % 2 == 0 then
      CrashModel.Boundary.before else .after))
    let start : State := { initial with faults.script := script }
    let (result, state) := (CrashM.restart 24 (attempt nested 7)).run start
    assertOutcome (← outcome result) (.ok 46)
    assertTrue state.faults.script.isEmpty "Restart reset the fault script"
    assertEq state.durable.pending []⟩,
  ⟨"crash/retry-exhaustion-retains-state", do
    let start : State := { initial with faults.script := List.replicate 3 (some .after) }
    let (result, stopped) := (CrashM.restart 1 (attempt nested 7)).run start
    assertTrue (match result with | .error .stopped => true | _ => false)
      "Retry exhaustion was not a crash"
    assertEq stopped.faults.calls 2
    let (resumed, _) := (CrashM.restart 1 (attempt nested 7)).run stopped
    assertOutcome (← outcome resumed) (.ok 46)⟩,
  ⟨"crash/completed-restart", do
    let (_, completed) := (attempt nested 7).run initial
    let start := { completed with faults := ⟨[some .after], 0⟩ }
    let (result, state) := (CrashM.restart 1 (attempt nested 7)).run start
    assertOutcome (← outcome result) (.ok 46)
    assertEq state.faults.calls 2 "Completed restart executed more than queue polls"
    assertEq state.durable.pending []⟩,
  ⟨"crash/interpreter-fuel-is-not-a-crash", do
    let (result, state) := (CrashM.restart 10 (attempt nested 7 false 0)).run initial
    assertOutcome (← outcome result) (.error ⟨.protocol, "Interpreter fuel exhausted"⟩)
    assertEq state.faults.calls 0
    assertEq state.durable.pending [Location.root]⟩
]

def generatedCases : Array TestCase := (Array.range 32).map fun seed =>
  let tree := (generate (3 + seed % 3) seed).1
  ⟨s!"crash/generated/{seed}", sweep (lowerPure tree) (lowerPure tree)⟩

end LeanCloudTests.Crashes
