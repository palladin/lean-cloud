import LeanCloudTests.Crash
import LeanCloudTests.LeaseQueue

namespace LeanCloudTests.LeasedReplay
open Lean LeanCloud

structure Durable where
  records : List (String × Json) := []
  transport : LeaseQueueModel.State Location := {}
  completed : Option Exit := none

abbrev M := CrashModel.M Durable
abbrev State := CrashModel.State Durable
abbrev Worker := LeaseQueue.Worker Unit LeaseQueueModel.Receipt

def db : Db Unit M where
  get key handle := do
    let value ← CrashModel.atomic fun state => (state.records.lookup key, state)
    return (value, handle)
  put key value handle := do
    let result ← CrashModel.atomic fun state =>
      (true, { state with records := (key, value) :: state.records.filter (·.1 != key) })
    return (result, handle)

def noBlobs : BlobStorage Unit M where
  putBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
  readBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩
  resolveBlob _ := throw ⟨.unsupported, "Unexpected blob operation"⟩

/-- Test environment: one unit of time passes before each transport poll. The
primitive queue itself never advances time. Set `pollTime` to zero to freeze it. -/
def transport (pollTime : Nat := 1) (duplicate : Bool := false) :
    LeaseQueue Unit M LeaseQueueModel.Receipt where
  enqueue location handle := do
    let _ ← CrashModel.atomic fun state =>
      let (_, next) := LeaseQueueModel.enqueue location state.transport
      ((), { state with transport := next })
    if duplicate then
      let _ ← CrashModel.atomic fun state =>
        let (_, next) := LeaseQueueModel.enqueue location state.transport
        ((), { state with transport := next })
    return ((), handle)
  dequeue handle := do
    -- This explicit environment tick is independent of catching a crash.
    modify fun state =>
      { state with durable.transport := LeaseQueueModel.advance pollTime state.durable.transport }
    let delivery ← CrashModel.atomic fun state =>
      let (delivery, next) := LeaseQueueModel.dequeue 3 state.transport
      (delivery.map (fun d => (d.value, d.receipt)), { state with transport := next })
    return (delivery, handle)
  acknowledge receipt handle := do
    let accepted ← CrashModel.atomic fun state =>
      let (accepted, next) := LeaseQueueModel.acknowledge receipt state.transport
      (accepted, { state with transport := next })
    return (accepted, handle)

def readCompleted : StateT Unit M (Option Exit) := fun handle => do
  return (← CrashModel.atomic (fun state => (state.completed, state)), handle)

def writeCompleted (outcome : Exit) : StateT Unit M Unit := fun handle => do
  let _ ← CrashModel.atomic fun state => ((), { state with completed := some outcome })
  return ((), handle)

def queue (pollTime : Nat := 1) (duplicate : Bool := false) : WorkQueue Worker M :=
  (transport pollTime duplicate).toWorkQueue readCompleted writeCompleted

def initial : State := ⟨{ transport := (LeaseQueueModel.enqueue Location.root {}).2 }, {}⟩

def attempt [Codec α] (program : Nat → Cloud M α) (input : Nat)
    (duplicate : Bool := false) : M (Except CloudError α) :=
  Prod.fst <$> (interpret (LeaseQueue.db (JournalDb.ofDb db)) (LeaseQueue.blobs noBlobs)
    (queue 1 duplicate) 10000 program input).run ⟨(), none⟩

def live (state : Durable) : Array Location :=
  state.transport.messages.filterMap (fun message => message.map (·.value))

def receive : IO (Worker × State) := do
  let (result, state) := ((queue 0).next ⟨(), none⟩).run initial
  let (work, worker) ← Leases.success result
  match work with
  | .item location => assertEq location Location.root
  | _ => throw (IO.userError "Root delivery missing")
  return (worker, state)

/-- Interrupt every primitive of a full replay, including individual enqueues,
acknowledgements and final-result publication, then restart with fresh local state. -/
def sweep (program : Nat → Cloud M Nat) (directProgram : Nat → Cloud Id Nat) : IO Unit := do
  let (expected, _) := (DirectInterpreter.interpret
    (Proofs.noBlobs : BlobStorage Unit Id) directProgram 7).run ()
  let action := attempt program 7
  let (baseline, finished) := action.run initial
  assertOutcome (← Crashes.outcome baseline) expected
  assertTrue (live finished.durable).isEmpty "Uninterrupted run failed to acknowledge work"
  for boundary in [CrashModel.Boundary.before, .after] do
    for cut in [:finished.faults.calls] do
      try
        let start := { initial with faults.script := List.replicate cut none ++ [some boundary] }
        let (result, stopped) := (CrashM.restart 0 action).run start
        Leases.crashed result
        assertEq stopped.faults.calls (cut + 1)
        let (resumed, recovered) := (CrashM.restart 0 action).run stopped
        assertOutcome (← Crashes.outcome resumed) expected
        assertEq recovered.durable.completed finished.durable.completed
        let (automatic, _) := (CrashM.restart 1 action).run start
        assertOutcome (← Crashes.outcome automatic) expected
      catch error => throw (IO.userError s!"call={cut}, boundary={reprStr boundary}: {error}")

def failing {m : Type → Type} (input : Nat) : Cloud m Nat := cloud {
  let _ ← Cloud.parallel #[Crashes.nested input, Cloud.fail "left failure", Cloud.fail "right failure"]
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
  ⟨"leased-replay/sweep/nested", sweep Crashes.nested Crashes.nested⟩,
  ⟨"leased-replay/sweep/failure", sweep failing failing⟩,
  ⟨"leased-replay/sweep/value", sweep (fun n => pure n) (fun n => pure n)⟩,
  ⟨"leased-replay/sweep/empty", sweep
    (fun _ => do let xs ← Cloud.parallel (#[] : Array (Cloud M Nat)); return xs.size)
    (fun _ => do let xs ← Cloud.parallel (#[] : Array (Cloud Id Nat)); return xs.size)⟩,
  ⟨"leased-replay/sweep/recorded-values", sweep recorded (fun n => pure (3 * n + 4))⟩,
  ⟨"leased-replay/duplicate-publication", do
    let (result, _) := (attempt Crashes.nested 7 true).run initial
    assertOutcome (← Crashes.outcome result) (.ok 46)⟩,
  ⟨"leased-replay/duplicate-failure", do
    let (result, _) := (attempt failing 7 true).run initial
    assertOutcome (← Crashes.outcome result) (.error ⟨.application, "left failure"⟩)⟩,
  ⟨"leased-replay/duplicate-recorded-values", do
    let (result, _) := (attempt recorded 7 true).run initial
    assertOutcome (← Crashes.outcome result) (.ok 25)⟩,
  ⟨"leased-replay/repeated-crashes", do
    let script := (List.replicate 20 [none, none, some CrashModel.Boundary.after]).flatten
    let start := { initial with faults.script := script }
    let (result, _) := (CrashM.restart 20 (attempt Crashes.nested 7)).run start
    assertOutcome (← Crashes.outcome result) (.ok 46)⟩,
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
    let start := { state with faults.script := [some .after] }
    let update := StepResult.runnable #[Location.root.child 0, Location.root.child 1]
    let (result, stopped) := ((queue 0).complete Location.root update worker).run start
    Leases.crashed result
    assertEq (live stopped.durable) #[Location.root, Location.root.child 0]
      "Successor publication was grouped atomically or acknowledged too early"
    let some (_, receipt) := worker.delivery | throw (IO.userError "Receipt missing")
    assertTrue (LeaseQueueModel.current receipt stopped.durable.transport).isSome
      "Incomplete publication acknowledged the parent"⟩,
  ⟨"leased-replay/final-result-before-ack", do
    let (worker, state) ← receive
    let start := { state with faults.script := [some .after] }
    let exit := Exit.success (toJson (42 : Nat))
    let (result, stopped) := ((queue 0).complete Location.root (.done exit) worker).run start
    Leases.crashed result
    assertEq stopped.durable.completed (some exit)
    assertEq (live stopped.durable) #[Location.root]
    let (resumed, final) := (attempt (fun _ => pure (42 : Nat)) 7).run stopped
    assertOutcome (← Crashes.outcome resumed) (.ok 42)
    assertEq final.faults.calls (stopped.faults.calls + 1)
      "Completed restart polled the transport instead of reading the saved result"⟩,
  ⟨"leased-replay/stale-ack-retains-new-delivery", do
    let (worker, state) ← receive
    let (delivery, transport) := LeaseQueueModel.dequeue 3
      (LeaseQueueModel.advance 3 state.durable.transport)
    let delivery ← Leases.required delivery
    let state := { state with durable.transport := transport }
    let (result, finished) :=
      ((queue 0).complete Location.root (.runnable #[Location.root.next]) worker).run state
    let (_, worker) ← Leases.success result
    assertTrue worker.delivery.isNone "Worker retained a rejected receipt"
    assertEq (live finished.durable) #[Location.root, Location.root.next]
    assertTrue (LeaseQueueModel.current delivery.receipt finished.durable.transport).isSome
      "Stale acknowledgement removed the newer delivery"⟩,
  ⟨"leased-replay/foreign-completion-is-ignored", do
    let (worker, state) ← receive
    let (result, finished) :=
      ((queue 0).complete Location.root.next (.runnable #[Location.root.next]) worker).run state
    let (_, after) ← Leases.success result
    assertEq after.delivery worker.delivery
    assertEq finished.faults.calls state.faults.calls
    assertEq (live finished.durable) #[Location.root]⟩
]

def generatedCases : Array TestCase := (Array.range 16).map fun seed =>
  let tree := (generate (3 + seed % 3) seed).1
  ⟨s!"leased-replay/generated/{seed}", sweep (Crashes.lowerPure tree) (Crashes.lowerPure tree)⟩

end LeanCloudTests.LeasedReplay
