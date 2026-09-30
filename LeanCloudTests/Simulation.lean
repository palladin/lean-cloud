import LeanCloudTests.Support

namespace LeanCloudTests.Simulated
open Lean LeanCloud
open Simulation

abbrev Machine (α : Type) := Simulation.State SimulationBackend.Durable α 2
abbrev Start (α : Type) := Fin 2 → SimulationBackend.M α

def applyEvent (start : Start α) (event : Event 2) (state : Machine α) :
    Except String (Machine α) :=
  (Simulation.step start SimulationBackend.advance event state).mapError reprStr

def nextEvent (state : Machine α) (worker : Fin 2) : Option (Event 2) :=
  match (state.workers worker).phase with
  | .waiting => some (.commit worker)
  | .responding => some (.resume worker)
  | .stopped => some (.restart worker)
  | .finished => none

/-- The bound belongs to the test driver, not to the workflow error channel. -/
def runWorker (budget : Nat) (start : Start α) (worker : Fin 2) (state : Machine α) :
    Except String (Machine α) := do
  let some event := nextEvent state worker | return state
  match budget with
  | 0 => throw "Simulation event budget exhausted"
  | budget + 1 => runWorker budget start worker (← applyEvent start event state)

/-- Preserve every suspension, including committed replies, for interruption sweeps. -/
def prefixes (budget : Nat) (start : Start α) (worker : Fin 2) (state : Machine α) :
    Except String (List (Machine α)) := do
  let some event := nextEvent state worker | return []
  match budget with
  | 0 => throw "Prefix enumeration budget exhausted"
  | budget + 1 =>
    return state :: (← prefixes budget start worker (← applyEvent start event state))

/-- Enumerate every enabled worker selection for a short, fixed event prefix.
This explores commit and response delivery separately, without claiming to
enumerate unbounded executions or every possible crash schedule. -/
def frontiers (depth : Nat) (start : Start α) (state : Machine α) :
    Except String (List (Machine α)) := do
  match depth with
  | 0 => return [state]
  | depth + 1 =>
    let mut found := []
    for worker in [0, 1] do
      if let some event := nextEvent state worker then
        found := found ++ (← frontiers depth start (← applyEvent start event state))
    return if found.isEmpty then [state] else found

/-- Reproducible worker selection, independent of queue selection. Both commit
and reply delivery can be interleaved. Crashes leave the other worker running. -/
def drive (budget : Nat) (start : Start α) (state : Machine α) (seed : Nat)
    (crashAt : List Nat := []) (index : Nat := 0) : Except String (Machine α) := do
  if (state.workers 0).phase == .finished && (state.workers 1).phase == .finished then
    return state
  match budget with
  | 0 => throw "Simulation event budget exhausted"
  | budget + 1 =>
    let seed := (1664525 * seed + 1013904223) % 4294967296
    let chosen : Fin 2 := if seed / 65536 % 2 == 0 then 0 else 1
    let worker := if (state.workers chosen).phase == .finished then
      (if chosen == 0 then 1 else 0 : Fin 2) else chosen
    let state ← if index % 32 == 0 then applyEvent start (.advanceTime 1) state else pure state
    let state ← if crashAt.contains index && (state.workers worker).phase != .stopped then do
      let state ← applyEvent start (.crash worker) state
      applyEvent start (.advanceTime 100) state
    else
      let some event := nextEvent state worker | throw "No runnable worker"
      applyEvent start event state
    drive budget start state seed crashAt (index + 1)

universe u

def workflow {m : Type → Type u} (variant input : Nat) : Cloud m Nat := cloud {
  match variant % 6 with
  | 0 =>
    let (x, y) ← cloud { return input + 1 } || cloud { return input + 2 }
    return x + y
  | 1 =>
    let values ← Cloud.parallel #[cloud {
      let values ← Cloud.parallel #[pure input, pure (input + 1)]
      return values.foldl (· + ·) 0
    }, pure (input * 2), cloud { return input + 3 }]
    return values.foldl (· + ·) 0
  | 2 =>
    let empty ← Cloud.parallel (α := Nat) #[]
    let values ← Cloud.parallel #[pure empty.size, pure input]
    return values.foldl (· + ·) 0
  | 3 =>
    let _ ← Cloud.parallel #[pure input, Cloud.fail "first failure", Cloud.fail "second failure"]
    return input
  | 4 =>
    let first ← Cloud.parallel #[pure input, pure (input + 4)]
    let next ← Cloud.parallel (first.map fun value => cloud { return value * value })
    return next.foldl (· + ·) 0
  | _ =>
    let _ ← Cloud.parallel #[cloud {
      let _ ← Cloud.parallel #[pure input, Cloud.fail "nested failure"]
      return input
    }, Cloud.fail "later failure"]
    return input
}

abbrev Outcome := Except CloudError Nat × SimulationBackend.Worker

def start (variant input : Nat) : Start Outcome := fun _ =>
  SimulationBackend.attempt 10000 100 (workflow variant) input

def expected (variant input : Nat) : Except CloudError Nat :=
  ((DirectInterpreter.interpret (Proofs.noBlobs : BlobStorage Unit Id)
    (workflow variant) input).run ()).1

def checkFinished (state : Machine Outcome) (outcome : Except CloudError Nat) : IO Unit := do
  for worker in [0, 1] do
    let some (actual, _) := (state.workers worker).outcome?
      | throw (IO.userError s!"Worker {worker.val} did not finish")
    assertOutcome actual outcome
  let encoded := match outcome with
    | .ok value => Exit.success (toJson value)
    | .error error => Exit.failure error
  assertEq state.durable.completed (some encoded) "Final result was not durable"

def generatedCases : Array TestCase :=
  (Array.range 6).flatMap fun variant =>
    (Array.range 8).flatMap fun seed =>
      #[false, true].map fun crashes =>
        ⟨s!"simulation/replay/{variant}/seed/{seed}/crashes/{crashes}", do
          let start := start variant (seed + 7)
          let initial := Simulation.State.initial SimulationBackend.initial start
          let .ok finished := drive 20000 start initial seed (if crashes then [11, 47, 113] else [])
            | throw (IO.userError "Replay simulation did not finish")
          checkFinished finished (expected variant (seed + 7))⟩

def primitiveCases : Array TestCase := #[
  ⟨"simulation/response-retains-original-read", do
    let start : Fin 2 → SimM Nat Nat := fun worker =>
      if worker == 0 then SimM.atomic fun value => (value, value)
      else SimM.atomic fun value => (value + 10, value + 10)
    let initial := Simulation.State.initial 3 start
    let .ok finished := Simulation.run start (fun _ state => state)
        [.commit 0, .commit 1, .resume 1, .resume 0] initial
      | throw (IO.userError "Invalid schedule")
    assertEq finished.durable 13
    assertEq (finished.workers 0).outcome? (some 3)
    assertEq (finished.workers 1).outcome? (some 13)⟩,
  ⟨"simulation/crash-discards-local-state", do
    let action : StateT Nat (SimM Nat) Nat := do
      modify (· + 1)
      let _ ← liftM (SimM.atomic fun durable : Nat => ((), durable + 1))
      let value ← get
      let _ ← liftM (SimM.atomic fun durable : Nat => ((), durable))
      return value
    let start : Fin 2 → SimM Nat (Nat × Nat) := fun _ => action.run 0
    let initial := Simulation.State.initial 0 start
    let .ok finished := Simulation.run start (fun _ state => state)
        [.commit 0, .resume 0, .crash 0, .restart 0,
         .commit 0, .resume 0, .commit 0, .resume 0] initial
      | throw (IO.userError "Invalid schedule")
    assertEq finished.durable 2 "Restart resumed the old continuation"
    assertEq (finished.workers 0).outcome? (some (1, 1)) "Local state survived restart"
    assertEq (finished.workers 1).phase .waiting "Crash affected another worker"⟩,
  ⟨"simulation/invalid-schedule-and-pause", do
    let start : Fin 2 → SimM Nat Nat := fun _ => SimM.atomic fun value => (value, value)
    let initial := Simulation.State.initial 5 start
    match Simulation.step start (fun _ state => state) (.resume 0) initial with
    | .error error => assertEq error .notResponding
    | .ok _ => throw (IO.userError "Resumed a worker before commit")
    match Simulation.step start (fun _ state => state) (.restart 0) initial with
    | .error error => assertEq error .notStopped
    | .ok _ => throw (IO.userError "Restarted a live worker")
    let .ok paused := Simulation.run start (fun _ state => state) [.commit 0] initial
      | throw (IO.userError "Invalid schedule")
    assertEq (paused.workers 0).phase .responding
    assertEq (paused.workers 0).outcome? none
    match Simulation.step start (fun _ state => state) (.commit 0) paused with
    | .error error => assertEq error .notWaiting
    | .ok _ => throw (IO.userError "Committed the same request twice")⟩,
  ⟨"simulation/lost-dequeue-reply-and-expiry", do
    let start : Start (Option (Location × LeaseQueueModel.Receipt) × Unit) := fun _ =>
      (SimulationBackend.transport 10).dequeue ()
    let initial := Simulation.State.initial SimulationBackend.initial start
    let .ok paused := Simulation.run start SimulationBackend.advance
        [.commit 0, .crash 0, .commit 1, .resume 1] initial
      | throw (IO.userError "Invalid schedule")
    assertEq (paused.workers 1).outcome? (some (none, ())) "Crash released a lease"
    assertEq paused.durable.transport.now 0 "Crash advanced the clock"
    let .ok finished := Simulation.run start SimulationBackend.advance
        [.advanceTime 10, .restart 0, .commit 0, .resume 0] paused
      | throw (IO.userError "Invalid schedule")
    let some (some (location, receipt), _) := (finished.workers 0).outcome?
      | throw (IO.userError "Expired delivery was not recovered")
    assertEq location Location.root
    assertEq receipt.generation 2
    let stale : LeaseQueueModel.Receipt := ⟨receipt.message, 1⟩
    let ackStart : Start (Bool × Unit) := fun _ => (SimulationBackend.transport 10).acknowledge stale ()
    let .ok rejected := runWorker 10 ackStart 0 (Simulation.State.initial finished.durable ackStart)
      | throw (IO.userError "Acknowledgement did not finish")
    assertEq (rejected.workers 0).outcome? (some (false, ()))
    assertEq rejected.durable finished.durable "Stale acknowledgement deleted a new delivery"⟩
]

def cases : Array TestCase := primitiveCases ++ #[
  ⟨"simulation/replay/bounded-interleavings", do
    let start := start 0 7
    let initial := Simulation.State.initial SimulationBackend.initial start
    let .ok states := frontiers 8 start initial
      | throw (IO.userError "Could not enumerate interleavings")
    assertEq states.length 256
    for (state, index) in states.zipIdx do
      let .ok finished := drive 20000 start state index
        | throw (IO.userError s!"Interleaving {index} did not finish")
      checkFinished finished (expected 0 7)⟩,
  ⟨"simulation/replay/ancestor-completes-after-parent-check", do
    let left := Exit.success (toJson (1 : Nat))
    let right := Exit.success (toJson (2 : Nat))
    let initial : SimulationBackend.Durable := { records := [
      (JournalDb.forkKey Location.root.key, toJson (2 : Nat)),
      (JournalDb.childKey Location.root.key 0, toJson left)] }
    let program : Cloud SimulationBackend.M Json :=
      Codec.encode <$> Cloud.parallel (α := Nat) #[pure 1, pure 2]
    let start : Start (Except CloudError StepResult × SimulationBackend.Worker) := fun worker =>
      (if worker == 0 then
        ReplayInterpreter.Internal.step SimulationBackend.db SimulationBackend.noBlobs 100
          program (Location.root.child 1)
      else ReplayInterpreter.Internal.finish SimulationBackend.db (Location.root.child 1) right).run ⟨(), none⟩
    -- Four reads reconstruct the incomplete parent. The next read belongs to
    -- traversal, after the entry-point guard has already accepted this child.
    let .ok paused := Simulation.run start SimulationBackend.advance
        (List.replicate 4 [.commit 0, .resume 0]).flatten (Simulation.State.initial initial start)
      | throw (IO.userError "Could not pause after the parent check")
    let .ok completed := runWorker 200 start 1 paused
      | throw (IO.userError "Other worker failed to complete the group")
    let .ok finished := runWorker 200 start 0 completed
      | throw (IO.userError "Paused worker did not resume")
    let some (.ok (.runnable locations), _) := (finished.workers 0).outcome?
      | throw (IO.userError "Obsolete child was reported as divergence")
    assertEq locations #[Location.root]⟩,
  ⟨"simulation/replay/expired-live-worker", do
    let start := start 1 7
    let initial := Simulation.State.initial SimulationBackend.initial start
    -- A receives root and pauses inside the interpreter. B then leases that
    -- same message while A retains its old receipt and continuation.
    let .ok shared := Simulation.run start SimulationBackend.advance
        [.commit 0, .resume 0, .commit 0, .resume 0, .advanceTime 100,
         .commit 1, .resume 1, .commit 1, .resume 1] initial
      | throw (IO.userError "Invalid duplicate-delivery schedule")
    let some (some root) := shared.durable.transport.messages[0]?
      | throw (IO.userError "Root message disappeared")
    assertEq root.generation 2
    assertEq (shared.workers 0).phase .waiting
    assertEq (shared.workers 1).phase .waiting
    let .ok finished := drive 20000 start shared 31
      | throw (IO.userError "Concurrent duplicate execution did not finish")
    checkFinished finished (expected 1 7)⟩,
  ⟨"simulation/replay/crash-at-every-boundary", do
    for variant in [0, 2, 3] do
      let start := start variant 7
      let initial := Simulation.State.initial SimulationBackend.initial start
      let .ok cuts := prefixes 2000 start 0 initial
        | throw (IO.userError "Could not enumerate replay boundaries")
      assertTrue (cuts.length > 20) "Replay did not exercise backend operations"
      for (paused, index) in cuts.zipIdx do
        let .ok stopped := Simulation.run start SimulationBackend.advance
            [.crash 0, .advanceTime 100, .restart 0] paused
          | throw (IO.userError s!"Invalid crash at boundary {index}")
        assertEq stopped.durable.records paused.durable.records "Crash erased records"
        let .ok finished := drive 20000 start stopped (index + 13)
          | throw (IO.userError s!"Recovery failed at boundary {index}")
        checkFinished finished (expected variant 7)⟩,
  ⟨"simulation/siblings/every-first-worker-boundary", do
    let initial : SimulationBackend.Durable := {
      records := [(JournalDb.forkKey Location.root.key, toJson (2 : Nat))] }
    let start : Start (Except CloudError StepResult × SimulationBackend.Worker) := fun worker =>
      (ReplayInterpreter.Internal.finish SimulationBackend.db (Location.root.child worker.val)
        (.success (toJson (worker.val + 1)))).run ⟨(), none⟩
    let initial := Simulation.State.initial initial start
    let .ok cuts := prefixes 200 start 0 initial
      | throw (IO.userError "Could not enumerate sibling boundaries")
    for (paused, index) in cuts.zipIdx do
      let .ok other := runWorker 200 start 1 paused
        | throw (IO.userError s!"Other sibling failed at boundary {index}")
      let .ok finished := runWorker 200 start 0 other
        | throw (IO.userError s!"Paused sibling failed at boundary {index}")
      let mut wakes := false
      for worker in [0, 1] do
        let some (.ok (.runnable locations), _) := (finished.workers worker).outcome?
          | throw (IO.userError "Sibling failed to finish")
        wakes := wakes || locations.contains Location.root
        assertEq (finished.durable.records.lookup (JournalDb.childKey Location.root.key worker.val))
          (some (toJson (Exit.success (toJson (worker.val + 1)))))
      assertTrue wakes s!"Both siblings missed the parent wakeup at boundary {index}"⟩
]

end LeanCloudTests.Simulated
