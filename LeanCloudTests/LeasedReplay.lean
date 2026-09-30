import LeanCloudTests.Recovery
import LeanCloudTests.LeaseQueue

namespace LeanCloudTests.LeasedReplay
open Lean LeanCloud SimTest
universe u

abbrev M := SimulationBackend.M
abbrev Worker := SimulationBackend.Worker
abbrev queue := SimulationBackend.queue 100

def live (state : SimulationBackend.Durable) : Array Location :=
  state.transport.messages.filterMap (fun message => message.map (·.value))

/-- Exercise duplicate publication through the actual adapter. Each duplicate
is a separate atomic call, just as with a lost enqueue acknowledgement. -/
def duplicateQueue : WorkQueue Worker M :=
  let base := SimulationBackend.transport 100
  let duplicated := { base with enqueue := fun location => do
    base.enqueue location
    base.enqueue location }
  duplicated.toWorkQueue SimulationBackend.readCompleted SimulationBackend.writeCompleted

def attempt (program : Nat → Cloud M Nat) : M (Except CloudError Nat × Worker) :=
  (interpret SimulationBackend.db SimulationBackend.noBlobs duplicateQueue
    10000 program 7).run ⟨(), none⟩

def receive : IO (Worker × SimulationBackend.Durable) := do
  let ((work, worker), state) ← finish (queue.next ⟨(), none⟩) SimulationBackend.initial
  match work with
  | .item location => assertEq location Location.root
  | _ => throw (IO.userError "Root delivery missing")
  return (worker, state)

def failing {m : Type → Type u} (input : Nat) : Cloud m Nat := cloud {
  let _ ← Cloud.parallel #[RecoveryTests.nested input, Cloud.fail "left failure", Cloud.fail "right failure"]
  return input
}

def recorded (input : Nat) : Cloud M Nat := cloud {
  let values ← Cloud.parallel #[Cloud.pure (fun _ => input + 1), cloud {
    let n ← Cloud.pure (fun _ => input * 2)
    Cloud.pure (fun _ => n + 3)
  }]
  Cloud.pure (fun _ => values.foldl (· + ·) 0)
}

def cases : Array TestCase := #[
  ⟨"leased-replay/sweep/failure", RecoveryTests.sweep failing failing⟩,
  ⟨"leased-replay/sweep/recorded-values", RecoveryTests.sweep recorded (fun n => pure (3 * n + 4))⟩,
  ⟨"leased-replay/duplicate-publication", do
    let ((result, _), state) ← finish (attempt RecoveryTests.nested) SimulationBackend.initial
      SimulationBackend.advance 1
    assertOutcome result (.ok 46)
    assertEq state.completed (some (.success (toJson (46 : Nat))))⟩,
  ⟨"leased-replay/duplicate-failure", do
    -- Duplicating every successor of this nested workflow creates a large
    -- backlog. Driver events count both commit and reply for every primitive.
    let ((result, _), state) ← finish (attempt failing) SimulationBackend.initial
      SimulationBackend.advance 1 200000
    let error : CloudError := ⟨.application, "left failure"⟩
    assertOutcome result (.error error)
    assertEq state.completed (some (.failure error))⟩,
  ⟨"leased-replay/duplicate-recorded-values", do
    let ((result, _), state) ← finish (attempt recorded) SimulationBackend.initial
      SimulationBackend.advance 1
    assertOutcome result (.ok 25)
    assertEq state.completed (some (.success (toJson (25 : Nat))))⟩,
  ⟨"leased-replay/backend-handle-and-receipt", do
    let backend : Db Nat Id := {
      get := fun _ state => (none, state + 1)
      put := fun _ _ state => (true, state + 1) }
    let worker : LeaseQueue.Worker Nat Nat := ⟨4, some (Location.root, 99)⟩
    let (_, worker) := (LeaseQueue.db backend).get "key" worker
    let (_, worker) := (LeaseQueue.db backend).put "key" Json.null worker
    assertEq worker.backend 6
    assertEq worker.delivery (some (Location.root, 99))
    let error : CloudError := ⟨.missingBlob, "expected"⟩
    let backend : BlobStorage Nat Id := {
      putBlob := fun _ state => (.error error, state + 1)
      readBlob := fun _ state => (.error error, state + 1)
      resolveBlob := fun _ state => (.error error, state + 1) }
    let (result, after) := ((LeaseQueue.blobs backend).resolveBlob "missing").run worker
    assertOutcome result (.error error)
    assertEq after.backend 7
    assertEq after.delivery worker.delivery⟩,
  ⟨"leased-replay/crash-between-successors", do
    let (worker, state) ← receive
    let update := StepResult.runnable #[Location.root.child 0, Location.root.child 1]
    let action := queue.complete Location.root update worker
    let .ok stopped := events action SimulationBackend.advance [.commit 0, .crash 0] (SimTest.initial action state)
      | throw (IO.userError "Simulation schedule did not finish")
    assertEq (stopped.workers 0).phase .stopped
    assertEq (live stopped.durable) #[Location.root, Location.root.child 0]
      "Successor publication was grouped atomically or acknowledged too early"
    let some (_, receipt) := worker.delivery | throw (IO.userError "Receipt missing")
    assertTrue (LeaseQueueModel.current receipt stopped.durable.transport).isSome
      "Incomplete publication acknowledged the parent"⟩,
  ⟨"leased-replay/final-result-before-ack", do
    let (worker, state) ← receive
    let exit := Exit.success (toJson (42 : Nat))
    let action := queue.complete Location.root (.done exit) worker
    let .ok stopped := events action SimulationBackend.advance [.commit 0, .crash 0] (SimTest.initial action state)
      | throw (IO.userError "Simulation schedule did not finish")
    assertEq stopped.durable.completed (some exit)
    assertEq (live stopped.durable) #[Location.root]
    let restart := SimulationBackend.attempt 10000 100 (fun _ : Unit => pure (42 : Nat)) ()
    let .ok final := events restart SimulationBackend.advance [.commit 0, .resume 0]
      (SimTest.initial restart stopped.durable)
      | throw (IO.userError "Simulation schedule did not finish")
    assertOutcome (← value final).1 (.ok 42)
    assertEq final.durable stopped.durable
      "Completed restart polled the transport instead of reading the saved result"⟩,
  ⟨"leased-replay/stale-ack-retains-new-delivery", do
    let (worker, state) ← receive
    let (delivery, transport) := LeaseQueueModel.dequeue 100
      (LeaseQueueModel.advance 100 state.transport)
    let delivery ← Leases.required delivery
    let state := { state with transport }
    let ((_, worker), finished) ← finish
      (queue.complete Location.root (.runnable #[Location.root.next]) worker) state
    assertTrue worker.delivery.isNone "Worker retained a rejected receipt"
    assertEq (live finished) #[Location.root, Location.root.next]
    assertTrue (LeaseQueueModel.current delivery.receipt finished.transport).isSome
      "Stale acknowledgement removed the newer delivery"⟩,
  ⟨"leased-replay/foreign-completion-is-ignored", do
    let (worker, state) ← receive
    let action := queue.complete Location.root.next (.runnable #[Location.root.next]) worker
    let final := SimTest.initial action state
    -- No commit is needed: an unrelated completion issues no backend request.
    assertEq (final.workers 0).phase .finished
    let (_, after) ← value final
    assertEq after.delivery worker.delivery
    assertEq final.durable state⟩
]

end LeanCloudTests.LeasedReplay
