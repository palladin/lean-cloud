import LeanCloudTests.Generated
import LeanCloudTests.SimulationSupport

namespace LeanCloudTests.RecoveryTests
open Lean LeanCloud SimTest
universe u

abbrev M := SimulationBackend.M

def nested {m : Type → Type u} (input : Nat) : Cloud m Nat := cloud {
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

/-- Interrupt before every commit and before every reply, then restart the actual
leased interpreter with fresh local state. The simulator advances lease time
explicitly; restart itself leaves time and durable storage untouched. -/
def sweep [Codec α] [BEq α] [Repr α]
    (program : Nat → Cloud M α) (directProgram : Nat → Cloud Id α) : IO Unit := do
  let expected := ((DirectInterpreter.interpret
    (Proofs.noBlobs : BlobStorage Unit Id) directProgram 7).run ()).1
  let action := SimulationBackend.attempt 10000 100 program 7
  let initial := SimTest.initial action SimulationBackend.initial
  let .ok baseline := run 30000 action initial
    | throw (IO.userError "Simulation schedule did not finish")
  assertOutcome (← value baseline).1 expected
  let encoded := match expected with
    | .ok result => Exit.success (Codec.encode result)
    | .error error => Exit.failure error
  assertEq baseline.durable.completed (some encoded)
  let .ok boundaries := prefixes 30000 action initial
    | throw (IO.userError "Prefix enumeration did not finish")
  for checkpoint in boundaries do
    let .ok stopped := events action SimulationBackend.advance [.crash 0] checkpoint
      | throw (IO.userError "Simulation schedule did not finish")
    assertEq (stopped.workers 0).phase .stopped
    assertEq stopped.durable checkpoint.durable "Crash changed durable storage"
    let .ok restarted := events action SimulationBackend.advance [.advanceTime 100, .restart 0] stopped
      | throw (IO.userError "Simulation schedule did not finish")
    let .ok recovered := run 30000 action restarted
      | throw (IO.userError "Simulation schedule did not finish")
    assertOutcome (← value recovered).1 expected
    assertEq recovered.durable.completed (some encoded) "Recovered result was not durable"

mutual
  /-- Instantiate the same pure workflow definition in Id and SimM.
  Generated effect/blob leaves become ordinary values in this pure-only suite. -/
  def lowerPure {m : Type → Type u} (tree : Tree) (input : Nat) : Cloud m Nat :=
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

  def lowerPureChildren {m : Type → Type u} (children : List Tree) (input : Nat) :
      List (Cloud m Nat) :=
    match children with
    | [] => []
    | child :: rest => lowerPure child input :: lowerPureChildren rest input
  termination_by structural children
end

def cases : Array TestCase := #[
  ⟨"recovery/sweep/nested", sweep nested nested⟩,
  ⟨"recovery/sweep/value", sweep (fun n => pure n) (fun n => pure n)⟩,
  ⟨"recovery/sweep/failure", sweep
    (fun _ => Cloud.fail "expected" : Nat → Cloud M Nat)
    (fun _ => Cloud.fail "expected")⟩,
  ⟨"recovery/sweep/empty", sweep
    (fun _ => Cloud.parallel (#[] : Array (Cloud M Nat)))
    (fun _ => Cloud.parallel (#[] : Array (Cloud Id Nat)))⟩,
  ⟨"recovery/cloud-error-finishes-worker", do
    let error : CloudError := ⟨.application, "expected"⟩
    let action := SimulationBackend.attempt 10000 100
      (fun _ : Unit => Cloud.fail "expected" : Unit → Cloud M Nat) ()
    let .ok finished := run 30000 action (SimTest.initial action SimulationBackend.initial)
      | throw (IO.userError "Simulation schedule did not finish")
    assertEq (finished.workers 0).phase .finished
    assertOutcome (← value finished).1 (.error error)
    assertEq finished.durable.completed (some (.failure error))⟩,
  ⟨"recovery/crash-is-not-a-cloud-error", do
    let program (_ : Nat) : Cloud M Nat := Cloud.exec fun _ =>
      SimM.atomic fun state => (42, { state with records := ("test/exec", toJson (42 : Nat)) :: state.records })
    let action := SimulationBackend.attempt 10000 100 program 0
    let .ok states := prefixes 30000 action (SimTest.initial action SimulationBackend.initial)
      | throw (IO.userError "Simulation schedule did not finish")
    let some checkpoint := states.find? (fun state => state.durable.records.lookup "test/exec" == some (toJson (42 : Nat)))
      | throw (IO.userError "Exec commit missing")
    assertEq (checkpoint.workers 0).phase .responding
    let .ok stopped := events action SimulationBackend.advance [.crash 0] checkpoint
      | throw (IO.userError "Simulation schedule did not finish")
    assertEq (stopped.workers 0).phase .stopped
    assertTrue (stopped.workers 0).outcome?.isNone "Crash became a workflow result"
    assertEq stopped.durable.records [("test/exec", toJson (42 : Nat))]
      "Crash was journaled as a workflow error"
    assertEq stopped.durable.completed none⟩,
  ⟨"recovery/repeated-interruption", do
    let action := SimulationBackend.attempt 10000 100 nested 7
    let schedule := (List.replicate 24
      [Simulation.Event.commit 0, .crash 0, .advanceTime 100, .restart 0]).flatten
    let .ok state := events action SimulationBackend.advance schedule
        (SimTest.initial action SimulationBackend.initial)
      | throw (IO.userError "Invalid interruption schedule")
    let .ok finished := run 30000 action state
      | throw (IO.userError "Simulation schedule did not finish")
    assertOutcome (← value finished).1 (.ok 46)
    assertEq finished.durable.completed (some (.success (toJson (46 : Nat))))⟩,
  ⟨"recovery/paused-schedule-can-continue", do
    let action := SimulationBackend.attempt 10000 100 nested 7
    let .ok paused := events action SimulationBackend.advance [.commit 0]
      (SimTest.initial action SimulationBackend.initial)
      | throw (IO.userError "Simulation schedule did not finish")
    assertEq (paused.workers 0).phase .responding
    let .ok finished := run 30000 action paused
      | throw (IO.userError "Simulation schedule did not finish")
    assertOutcome (← value finished).1 (.ok 46)⟩,
  ⟨"recovery/completed-restart", do
    let action := SimulationBackend.attempt 10000 100 nested 7
    let (_, completed) ← finish action SimulationBackend.initial
    let .ok finished := events action SimulationBackend.advance
      [.commit 0, .crash 0, .restart 0, .commit 0, .resume 0] (SimTest.initial action completed)
      | throw (IO.userError "Simulation schedule did not finish")
    assertOutcome (← value finished).1 (.ok 46)
    assertEq finished.durable completed "Completed restart touched storage or transport"⟩,
  ⟨"recovery/interpreter-fuel-is-not-a-crash", do
    let action := SimulationBackend.attempt 0 100 nested 7
    let state := SimTest.initial action SimulationBackend.initial
    assertEq (state.workers 0).phase .finished
    assertOutcome (← value state).1 (.error ⟨.protocol, "Interpreter fuel exhausted"⟩)
    assertEq state.durable SimulationBackend.initial⟩
]

def generatedCases : Array TestCase := (Array.range 32).map fun seed =>
  let tree := (generate (3 + seed % 3) seed).1
  ⟨s!"recovery/generated/{seed}", sweep (lowerPure tree) (lowerPure tree)⟩

end LeanCloudTests.RecoveryTests
