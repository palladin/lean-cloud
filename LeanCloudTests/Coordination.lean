import LeanCloudTests.Support

namespace LeanCloudTests
open Lean LeanCloud

private def response (deliveries : Array Delivery) : WorkerMessage :=
  (deliveries[0]?).map (·.message) |>.getD .idle

private def assigned (deliveries : Array Delivery) : IO Assignment :=
  match response deliveries with
  | .execute assignment => pure assignment
  | other => throw (IO.userError s!"Expected assignment, got {reprStr other}")

private def rootRecord (value : Nat) : ReplayRecord :=
  ⟨ReplayStore.returnRequest, .success (toJson value)⟩

private def typedWorkflow (_ : Unit) : Cloud (SimM SimulationBackend.World) (Nat × String) := cloud {
  let captured ← Cloud.pure (fun _ => 7)
  cloud {
    let values ← Cloud.parallel #[cloud { return captured + 1 }, cloud { return captured + 2 }]
    return values.foldl (· + ·) 0
  } || cloud { return s!"value={captured}" }
}

def coordinationCases : Array TestCase := #[
  ⟨"replay/child-does-not-read-ancestor-joins", do
    let program (input : Nat) : Cloud IO (Array (Array Nat)) :=
      Cloud.parallel #[Cloud.parallel #[cloud { return input + 1 }, cloud { return input + 2 }]]
    let branch := Location.root.child 0 |>.child 1
    let key := ReplayStore.returnKey branch
    let saved ← IO.mkRef (none : Option ReplayRecord)
    let records : ReplayStore IO := {
      read := fun requested => do
        unless requested == key do
          throw (IO.userError s!"Child depends on an unrelated record: {requested}")
        saved.get
      create := fun requested proposed => do
        assertEq requested key
        saved.modifyGet fun existing =>
          let accepted := existing.getD proposed
          (accepted, some accepted) }
    let blobs : BlobStorage IO := {
      putBlob := fun _ => throw ⟨.unsupported, "Unexpected blob operation"⟩
      readBlob := fun _ => throw ⟨.unsupported, "Unexpected blob operation"⟩
      resolveBlob := fun _ => throw ⟨.unsupported, "Unexpected blob operation"⟩ }
    let result ← (ReplayInterpreter.step records blobs 100 program 7 ⟨0, branch, branch, false⟩).run
    assertOutcome result (.ok .done)
    assertEq (← saved.get) (some (rootRecord 9))⟩,
  ⟨"replay/typed-root-and-nested-child-codecs", do
    for chaos in [false, true] do
      let world ← differential typedWorkflow 71 chaos
      let resultAt (location : Location) := (world.records.lookup (ReplayStore.returnKey location)).map (·.outcome)
      let fork := Location.root.next
      assertEq (resultAt (fork.child 0 |>.child 1)) (some (.success (Codec.encode (9 : Nat))))
      assertEq (resultAt (fork.child 0)) (some (.success (Codec.encode (Sum.inl (17 : Nat) : Sum Nat String))))
      assertEq (resultAt (fork.child 1)) (some (.success (Codec.encode (Sum.inr "value=7" : Sum Nat String))))
      assertEq (resultAt Location.root) (some (.success (Codec.encode ((17 : Nat), "value=7"))))⟩,
  ⟨"scheduler/idempotent-request-and-report", do
    let (initial, first) := Scheduler.handle 10 {} (.ready "a/0")
    let assignment ← assigned first
    let (repeated, second) := Scheduler.handle 10 initial (.ready "a/0")
    assertEq initial repeated
    assertEq (← assigned second) assignment
    let report : Report := ⟨"a/0", assignment.attempt, .ok (.fork Location.root 2), #["prefix"]⟩
    let (forked, _) := Scheduler.handle 10 repeated (.report report)
    let (duplicate, _) := Scheduler.handle 10 forked (.report report)
    assertEq duplicate forked
    assertEq forked.jobs.size 3
    assertEq (forked.workers[0]?.map (·.recorded)) (some #["prefix"])⟩,
  ⟨"scheduler/stale-attempt-cannot-complete-new-assignment", do
    let (state, old) := Scheduler.handle 10 {} (.ready "a/0")
    let old ← assigned old
    let (state, _) := Scheduler.handle 10 state (.tick 10)
    let (state, fresh) := Scheduler.handle 10 state (.ready "a/1")
    let fresh ← assigned fresh
    assertTrue (fresh.attempt > old.attempt) "Reused an attempt number"
    let (state, _) := Scheduler.handle 10 state (.report ⟨"a/0", old.attempt, .ok .done, #[]⟩)
    assertTrue (!state.finished) "Accepted stale completion"
    let (state, _) := Scheduler.handle 10 state (.report ⟨"a/1", fresh.attempt, .ok .done, #[]⟩)
    assertTrue state.finished "Did not accept current completion"⟩,
  ⟨"scheduler/parallel-waits-for-all-children", do
    let (state, root) := Scheduler.handle 10 {} (.ready "a")
    let root ← assigned root
    let (state, _) := Scheduler.handle 10 state (.report ⟨"a", root.attempt, .ok (.fork Location.root 2), #[]⟩)
    let (state, first) := Scheduler.handle 10 state (.ready "a")
    let first ← assigned first
    let (state, second) := Scheduler.handle 10 state (.ready "b")
    let second ← assigned second
    let (state, _) := Scheduler.handle 10 state (.report ⟨"b", second.attempt, .ok .done, #[]⟩)
    assertEq state.jobs[0]!.status (.waiting #[Location.root.child 0, Location.root.child 1])
    let (state, _) := Scheduler.handle 10 state (.report ⟨"a", first.attempt, .ok .done, #[]⟩)
    let (_, joined) := Scheduler.handle 10 state (.ready "c")
    let joined ← assigned joined
    assertTrue joined.joining "Parent was not resumed for joining"
    assertEq joined.location Location.root⟩,
  ⟨"scheduler/empty-parallel-is-immediately-joinable", do
    let (state, root) := Scheduler.handle 10 {} (.ready "a")
    let root ← assigned root
    let (state, _) := Scheduler.handle 10 state (.report ⟨"a", root.attempt, .ok (.fork Location.root 0), #[]⟩)
    let (_, resumed) := Scheduler.handle 10 state (.ready "a")
    assertTrue (← assigned resumed).joining "Empty group remained suspended"⟩,
  ⟨"records/first-successful-create-wins", do
    let old : Fin 2 := ⟨0, by decide⟩
    let fresh : Fin 2 := ⟨1, by decide⟩
    let start : Simulation.Start SimulationBackend.World ReplayRecord 2 := fun actor _ =>
      SimulationBackend.records.create "key" (rootRecord (if actor == old then 99 else 7))
    -- The old request survives its crash. A fresh writer finishes first;
    -- then the old request arrives, and that writer retries after restart.
    let result := Simulation.run start
      [.crash old, .commit fresh, .resume fresh, .commitOrphan 0,
        .restart old, .commit old, .resume old]
      (Simulation.State.initial {} start)
    let (records, writes, returned) ← unwrap (result.map (fun state =>
      (state.world.records, state.world.writes, (Array.finRange 2).map fun actor =>
        match state.actors actor with | .finished record => some record | _ => none)) |>.mapError reprStr)
    assertEq records [("key", rootRecord 7)]
    assertEq writes 1
    assertEq returned #[some (rootRecord 7), some (rootRecord 7)]⟩,
  ⟨"protocol/json-roundtrip", do
    let report : Report := ⟨"worker/3", 17, .ok (.fork #[(0, 2), (1, 5)] 3), #["x", "y"]⟩
    let state : Scheduler.State := { workers := #[⟨"worker/3", #["x", "y"]⟩], nextAttempt := 18 }
    let decoded ← unwrap (Json.parse (toJson state).compress >>= fromJson? (α := Scheduler.State))
    assertEq decoded state
    let decoded ← unwrap (Json.parse (toJson report).compress >>= fromJson? (α := Report))
    assertEq (toJson decoded) (toJson report)
    let error : Report := ⟨"worker/3", 17, .error ⟨.divergence, "changed"⟩, #[]⟩
    let decoded ← unwrap (Json.parse (toJson error).compress >>= fromJson? (α := Report))
    assertEq (toJson decoded) (toJson error)⟩
]

private def workflow (_ : Unit) : Cloud (SimM SimulationBackend.World) Nat := cloud {
  let captured ← Cloud.pure (fun _ => 7)
  let values ← Cloud.parallel #[
    cloud { return captured * 2 },
    cloud {
      let nested ← Cloud.parallel #[cloud { return captured + 1 }, cloud { return captured + 2 }]
      return nested.foldl (· + ·) 0
    }]
  return values.foldl (· + ·) captured
}

/-- Find a real execution boundary in a running group, then kill that actor.
The remaining execution includes late orphan commits and fresh process ids. -/
private def crashAt (label : String) (afterCommit : Bool) (loseRequest := false) : Except String Machine := do
  let start := SimulationBackend.start (workers := 3) 100000 10000 1000 workflow ()
  let mut state := Simulation.State.initial {} start
  for _ in [:20000] do
    state := { state with world := SimulationBackend.networkStep (.deliver 0) state.world }
    for actor in Array.finRange 4 do
      match state.actors actor with
      | .waiting _ waitingLabel _ _ =>
        if waitingLabel.startsWith label && state.world.writes > 0 then
          if afterCommit then state ← event start (.commit actor) state
          let pending := state.orphans.size
          state ← event start (.crash actor) state
          if loseRequest then
            unless state.orphans.size == pending + 1 do throw "Crash did not leave an uncommitted remote request"
            state ← event start (.discardOrphan pending) state
          let finished ← runSystem start state 0 false
          return finished
      | _ => pure PUnit.unit
      state ← tick start actor state
  throw s!"Boundary not reached: {label}"

def crashBoundaryCases : Array TestCase :=
  let remote := #["record.create:0:0/return", "record.read", "worker.receive",
    "worker.send", "worker.acknowledge", "scheduler.receive", "scheduler.send", "scheduler.acknowledge"]
  let localOps := #["worker.observe", "worker.confirmed", "scheduler.load", "scheduler.save"]
  let check (label : String) (afterCommit loseRequest : Bool) : TestCase :=
    ⟨s!"crash/{label}/{if loseRequest then "before-lost" else if afterCommit then "after" else "before"}", do
      let world ← unwrap ((crashAt label afterCommit loseRequest).map (·.world))
      let some record := world.records.lookup (ReplayStore.returnKey Location.root)
        | throw (IO.userError "No final durable record")
      assertEq record.outcome (.success (toJson (38 : Nat)))⟩
  ((remote ++ localOps).flatMap fun label => #[check label false false, check label true false]) ++
    (remote.map fun label => check label false true)

def mailboxCases : Array TestCase := #[
  ⟨"mailbox/unacknowledged-delivery-survives-crash", do
    let inbox := MailboxModel.publish (42 : Nat) (MailboxModel.connect 0 {})
    let (first, reserved) := MailboxModel.receive 0 inbox
    assertEq (first.map (·.message)) (some 42)
    assertTrue reserved.pending.isEmpty "Delivery was not reserved"
    let recovered := MailboxModel.connect 1 (MailboxModel.disconnect 0 reserved)
    let (again, _) := MailboxModel.receive 1 recovered
    assertEq (again.map (·.message)) (some 42)⟩,
  ⟨"mailbox/stale-ack-cannot-remove-new-delivery", do
    let (_, reserved) := MailboxModel.receive 0 (MailboxModel.publish (42 : Nat) (MailboxModel.connect 0 {}))
    let (_, recovered) := MailboxModel.receive 1 (MailboxModel.connect 1 (MailboxModel.disconnect 0 reserved))
    let some delivery := recovered.inFlight | throw (IO.userError "No redelivery")
    let stale := MailboxModel.acknowledge 0 delivery.receipt recovered
    assertTrue stale.inFlight.isSome "Old session acknowledged new delivery"
    let accepted := MailboxModel.acknowledge 1 delivery.receipt recovered
    assertTrue accepted.inFlight.isNone "Current session could not acknowledge"
    assertTrue accepted.pending.isEmpty "Acknowledged delivery was requeued"⟩,
  ⟨"mailbox/late-receive-after-crash-cannot-reserve", do
    let inbox := MailboxModel.disconnect 0 (MailboxModel.publish (42 : Nat) (MailboxModel.connect 0 {}))
    let (delivery, after) := MailboxModel.receive 0 inbox
    assertTrue delivery.isNone "Dead consumer received a message"
    assertEq after.pending #[42]
    let lateOpen := MailboxModel.connect 0 after
    assertTrue (!lateOpen.connected) "Old connect reopened a dead session"⟩,
  ⟨"mailbox/confirmed-publication-survives-offline-consumer", do
    let inbox := MailboxModel.publish (42 : Nat) ({} : MailboxModel.Inbox Nat)
    let (delivery, _) := MailboxModel.receive 0 (MailboxModel.connect 0 inbox)
    assertEq (delivery.map (·.message)) (some 42)⟩
]

private def recoveringScheduler : Scheduler.State := {
  jobs := #[
    ⟨Location.root, Location.root, false,
      .waiting #[Location.root.child 0, Location.root.child 1]⟩,
    ⟨Location.root.child 0, Location.root.child 0, false, .running "worker-1" 11 100000⟩,
    ⟨Location.root.child 1, Location.root.child 1, false, .done⟩]
  workers := #[⟨"worker-1", #["saved-prefix"]⟩]
  nextAttempt := 12
  now := 7 }

private def recoveredScheduler : Scheduler.State :=
  { recoveringScheduler with
    jobs := recoveringScheduler.jobs.set! 1
      ({ recoveringScheduler.jobs[1]! with status := .pending }) }

def simulationBoundaryCases : Array TestCase := #[
  ⟨"simulation/scheduler-startup-recovers-assignments", do
    -- No actor turns: startup itself must reload and release old attempts,
    -- including one whose deadline exceeds the new process's timeout.
    let start := SimulationBackend.start (workers := 0) 0 100 10 workflow ()
    let (_, world) ← unwrap (evaluate 100 (start ⟨0, by decide⟩ 1)
      { scheduler := recoveringScheduler })
    assertEq world.scheduler recoveredScheduler
    let (_, again) ← unwrap (evaluate 100 (start ⟨0, by decide⟩ 2) world)
    assertEq again.scheduler recoveredScheduler "Recovery was not idempotent"
    let (_, deliveries) := Scheduler.handle 10 world.scheduler (.ready "replacement")
    let assignment ← assigned deliveries
    assertEq assignment.branch (Location.root.child 0)
    assertEq assignment.attempt 12⟩,
  ⟨"simulation/recovery-local-save-crash-boundaries", do
    let actor : Fin 1 := ⟨0, by decide⟩
    let start : Simulation.Start SimulationBackend.World Unit 1 := fun _ generation =>
      Scheduler.recover (SimulationBackend.schedulerPorts generation).localDb
    for afterCommit in #[false, true] do
      let initial := Simulation.State.initial { scheduler := recoveringScheduler } start
      let events := (if afterCommit then [.commit actor] else []) ++ [.crash actor]
      let crashed := do
        let atSave ← Simulation.run start [.commit actor, .resume actor] initial
        Simulation.run start events atSave
      let (world, noOrphans) ← unwrap (crashed.map (fun state => (state.world, state.orphans.isEmpty))
        |>.mapError reprStr)
      assertTrue noOrphans "Recovery save survived its process as an orphan"
      assertEq world.scheduler (if afterCommit then recoveredScheduler else recoveringScheduler)
      let (_, recovered) ← unwrap (evaluate 100 (start actor 1) world)
      assertEq recovered.scheduler recoveredScheduler⟩,
  ⟨"simulation/worker-crash-discards-only-local-observations", do
    let start := SimulationBackend.start (workers := 3) 0 100 10 workflow ()
    let record := rootRecord 7
    let world : SimulationBackend.World := {
      scheduler := recoveringScheduler
      records := [("saved-prefix", record)]
      observations := [("worker-1", #["saved-prefix"]), ("worker-2", #["other"])] }
    let crashed ← unwrap ((event start (.crash ⟨1, by decide⟩)
      (Simulation.State.initial world start)).map (·.world))
    assertEq (crashed.observations.lookup "worker-1") none
    assertEq (crashed.observations.lookup "worker-2") (some #["other"])
    assertEq crashed.scheduler world.scheduler "Worker crash changed durable scheduler metadata"
    assertEq crashed.records world.records "Worker crash removed global records"⟩,
  ⟨"simulation/remote-request-commits-after-crash", do
    let start : Simulation.Start Nat Nat 1 := fun _ _ => SimM.atomic (fun n => (n, n + 1))
    let result := Simulation.run start [.crash ⟨0, by decide⟩, .commitOrphan 0]
      (Simulation.State.initial 0 start)
    assertEq (← unwrap (result.map (·.world) |>.mapError reprStr)) 1⟩,
  ⟨"simulation/scheduler-local-write-dies-with-process", do
    let start : Simulation.Start Nat Nat 1 := fun _ _ => SimM.local (fun n => (n, n + 1))
    let result := Simulation.run start [.crash ⟨0, by decide⟩] (Simulation.State.initial 0 start)
    assertEq (← unwrap (result.map (fun state => (state.world, state.orphans.size)) |>.mapError reprStr)) (0, 0)⟩,
  ⟨"simulation/local-commit-survives-lost-reply", do
    let start : Simulation.Start Nat Nat 1 := fun _ _ => SimM.local (fun n => (n, n + 1))
    let result := Simulation.run start [.commit ⟨0, by decide⟩, .crash ⟨0, by decide⟩]
      (Simulation.State.initial 0 start)
    assertEq (← unwrap (result.map (·.world) |>.mapError reprStr)) 1⟩
]

end LeanCloudTests
