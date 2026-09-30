import LeanCloudTests.Simulation
import LeanCloud.Proofs.ConcurrentPublication

namespace LeanCloudTests.ConcurrentPublication
open Lean LeanCloud Simulation SimulationBackend Simulated
private abbrev Plan := Proofs.ConcurrentPublication.Request

private abbrev Return := Unit × SimulationBackend.Worker
private def answer : Exit := .success (toJson (33 : Nat))

private def request (slot : Nat) (locations : Array Location) : Plan :=
  ⟨Location.root.child slot, ⟨slot, 1⟩, .runnable locations⟩

private def requests (variant : Nat) : Fin 2 → Plan := fun worker =>
  match variant with
  | 0 => request worker.val #[Location.root]
  | 1 => request worker.val #[Location.root.child (worker.val + 2), Location.root.child (worker.val + 4)]
  | 2 => request 0 #[Location.root, Location.root.next]
  | 3 => request worker.val #[Location.root]
  | 4 => request worker.val #[]
  | _ => ⟨Location.root.child worker.val, ⟨worker.val, 1⟩, .done answer⟩

private def initial (variant : Nat) : Durable := {
  records := [("unchanged", toJson "journal")]
  transport := { messages := #[
    some ⟨Location.root.child 0, if variant == 3 then 2 else 1, 10⟩,
    some ⟨Location.root.child 1, 1, 10⟩,
    some ⟨Location.root.child 99, 0, 0⟩] } }

private def start (plan : Fin 2 → Plan) : Start Return := fun worker =>
  ((queue 10).complete (plan worker).location (plan worker).response).run
    ⟨(), some ((plan worker).location, (plan worker).receipt)⟩

private def retained (location : Location) (slot : Nat) (state : Durable) : Bool :=
  (state.transport.messages[slot]?).any fun item => item.any (·.value == location)

private def published (cutoff : Nat) (response : StepResult) (state : Durable) : Bool :=
  match response with
  | .runnable locations => locations.all fun location =>
    (state.transport.messages.extract cutoff state.transport.messages.size).any fun message =>
      message.any (·.value == location)
  | .done outcome => state.completed == some outcome

private def check (plan : Fin 2 → Plan) (state : Machine Return) : IO Unit := do
  assertEq state.durable.records [("unchanged", toJson "journal")]
  assertTrue (retained (Location.root.child 99) 2 state.durable) "Unrelated message was removed"
  for worker in [0, 1] do
    let req := plan worker
    assertTrue (retained req.location req.receipt.message state.durable || published 3 req.response state.durable)
      s!"Worker {worker.val} lost its incoming message before durable publication"
    if let some (_, handle) := (state.workers worker).outcome? then
      assertEq handle.delivery none "Returned publication retained a local receipt"
      assertTrue (published 3 req.response state.durable) "Returned publication is incomplete"

private def runChecked (plan : Fin 2 → Plan) (budget : Nat) (state : Machine Return)
    (seed : Nat) (crashes : List Nat := []) (stale : Bool := false) (index : Nat := 0) : IO Unit := do
  check plan state
  if (state.workers 0).phase == .finished && (state.workers 1).phase == .finished then
    if stale then
      assertTrue (retained (Location.root.child 0) 0 state.durable) "A stale receipt removed the newer delivery"
    return
  match budget with
  | 0 => throw (IO.userError "Publication test budget exhausted")
  | budget + 1 =>
    let seed := (1664525 * seed + 1013904223) % 4294967296
    let selected : Fin 2 := if seed / 65536 % 2 == 0 then 0 else 1
    let worker := if (state.workers selected).phase == .finished then
      (if selected == 0 then 1 else 0 : Fin 2) else selected
    let event ← if crashes.contains index && (state.workers worker).phase != .stopped then
      pure (.crash worker)
    else match nextEvent state worker with
      | some event => pure event
      | none => throw (IO.userError "No publication event available")
    let .ok next := applyEvent (start plan) event state
      | throw (IO.userError "Invalid publication schedule")
    runChecked plan budget next seed crashes stale (index + 1)

private def generatedCases : Array TestCase :=
  (Array.range 6).flatMap fun variant =>
    (Array.range 2).flatMap fun seed =>
      #[false, true].map fun crashes =>
        ⟨s!"simulation/publication/{variant}/seed/{seed}/crashes/{crashes}", do
          let plan := requests variant
          runChecked plan 300 (Simulation.State.initial (initial variant) (start plan)) seed
            (if crashes then [3, 9, 17, 25] else []) (variant == 3)⟩

private def boundaryCases : Array TestCase := #[
  ⟨"simulation/publication/every-first-worker-boundary", do
    for variant in [:6] do
      let plan := requests variant
      let action := start plan
      let .ok cuts := prefixes 100 action 0 (Simulation.State.initial (initial variant) action)
        | throw (IO.userError "Could not enumerate publication boundaries")
      for paused in cuts do
        check plan paused
        let .ok crashed := applyEvent action (.crash 0) paused
          | throw (IO.userError "Could not crash publication")
        assertEq crashed.durable paused.durable
        let .ok other := runWorker 100 action 1 crashed
          | throw (IO.userError "Other publisher did not finish")
        check plan other
        let _ ← runChecked plan 200 other 19
        pure ()⟩,
  ⟨"simulation/publication/all-ten-event-prefixes", do
    let plan := requests 1
    let action := start plan
    for depth in [:11] do
      let .ok cuts := frontiers depth action (Simulation.State.initial (initial 1) action)
        | throw (IO.userError "Could not enumerate publication schedules")
      for paused in cuts do check plan paused⟩,
  ⟨"simulation/publication/conflicting-plans-need-an-agreement-premise", do
    -- Deliberately violates Batch.duplicates: one caller discards the delivery
    -- while another intends to replace it. This is not a valid replay protocol.
    let plan := fun worker : Fin 2 => request 0 (if worker == 0 then #[] else #[Location.root])
    let action := start plan
    let .ok finished := runWorker 100 action 0 (Simulation.State.initial (initial 0) action)
      | throw (IO.userError "Empty publication did not finish")
    assertTrue (!(retained (plan 1).location (plan 1).receipt.message finished.durable))
      "The empty plan should have acknowledged the shared incoming slot"
    assertTrue (!(published 3 (plan 1).response finished.durable))
      "The conflicting replacement plan must not be considered published"⟩
]

private def workflow (_ : Unit) : Cloud SimulationBackend.M Nat := cloud {
  let values ← Cloud.parallel #[pure 11, pure 22]
  return values.foldl (· + ·) 0
}

private def replayStart : Start Simulated.Outcome := fun _ =>
  SimulationBackend.attempt 10000 10 workflow ()

private def replayInitial : Durable := {
  records := [(JournalDb.forkKey Location.root.key, toJson (2 : Nat)),
    (JournalDb.childKey Location.root.key 0, toJson (Exit.success (toJson (11 : Nat))))]
  transport := (LeaseQueueModel.enqueue (Location.root.child 1) {}).2 }

private def hasMessage (location : Location) (state : Durable) : Bool :=
  state.transport.messages.any fun message => message.any (·.value == location)

private def gap (kind : Nat) (before after : Durable) : Bool :=
  match kind with
  | 0 => !hasMessage Location.root before && hasMessage Location.root after &&
      retained (Location.root.child 1) 0 before
  | 1 => hasMessage Location.root before && retained (Location.root.child 1) 0 before &&
      !retained (Location.root.child 1) 0 after
  | _ => before.completed.isNone && after.completed.isSome

private def replayCases : Array TestCase :=
  #[("parent-enqueue", 0), ("child-acknowledgement", 1), ("final-result", 2)].map fun (name, kind) =>
    ⟨s!"simulation/publication/replay-gap/{name}", do
      let .ok cuts := prefixes 2000 replayStart 0 (Simulation.State.initial replayInitial replayStart)
        | throw (IO.userError "Could not enumerate replay handoff")
      let some paused := cuts.find? fun state =>
          match state.workers 0 with
          | .waiting operation _ => gap kind state.durable (operation state.durable).2
          | _ => false
        | throw (IO.userError s!"Missing {name} gap in replay")
      for loseReply in [false, true] do
        let selected := if loseReply then applyEvent replayStart (.commit 0) paused else .ok paused
        let .ok boundary := selected
          | throw (IO.userError "Could not commit handoff operation")
        let .ok crashed := applyEvent replayStart (.crash 0) boundary
          | throw (IO.userError "Could not crash at handoff boundary")
        assertEq crashed.durable boundary.durable
        let .ok restarted := Simulation.run replayStart SimulationBackend.advance
            [.advanceTime 10, .restart 0] crashed
          | throw (IO.userError "Could not restart with fresh worker state")
        let .ok finished := drive 20000 replayStart restarted 23
          | throw (IO.userError s!"Replay failed after {name}, lost reply = {loseReply}")
        Simulated.checkFinished finished (.ok 33)⟩

private def bothChildren : Durable := {
  records := [(JournalDb.forkKey Location.root.key, toJson (2 : Nat))]
  transport := (LeaseQueueModel.enqueue (Location.root.child 1)
    (LeaseQueueModel.enqueue (Location.root.child 0) {}).2).2 }

/-- The first child has computed an empty response and is about to acknowledge.
The second child's slot is still missing. -/
private def beforeEmptyAck : Except String (Machine Simulated.Outcome) := do
  let cuts ← prefixes 2000 replayStart 0 (Simulation.State.initial bothChildren replayStart)
  let some paused := cuts.find? fun state =>
      match state.workers 0 with
      | .waiting operation _ =>
        (state.durable.records.lookup (JournalDb.childKey Location.root.key 0)).isSome &&
        (state.durable.records.lookup (JournalDb.childKey Location.root.key 1)).isNone &&
        !hasMessage Location.root state.durable && retained (Location.root.child 0) 0 state.durable &&
        !retained (Location.root.child 0) 0 (operation state.durable).2
      | _ => false
    | throw "Could not find the first child's empty acknowledgement"
  return paused

private def changingResponseCases : Array TestCase := #[
  ⟨"simulation/publication/empty-reply-after-parent-consumed", do
    let .ok paused := beforeEmptyAck
      | throw (IO.userError "Missing empty-reply boundary")
    let .ok other := runWorker 2000 replayStart 1 paused
      | throw (IO.userError "Other worker did not consume the parent")
    assertEq other.durable.completed (some answer)
    assertTrue (!hasMessage Location.root other.durable) "The parent was not consumed"
    assertTrue (retained (Location.root.child 0) 0 other.durable) "Paused child's delivery disappeared"
    let .ok finished := runWorker 2000 replayStart 0 other
      | throw (IO.userError "Old empty response did not resume")
    assertTrue (!retained (Location.root.child 0) 0 finished.durable) "Old empty response did not acknowledge"
    Simulated.checkFinished finished (.ok 33)⟩,
  ⟨"simulation/publication/retry-changes-empty-reply-to-wakeup", do
    let .ok paused := beforeEmptyAck
      | throw (IO.userError "Missing empty-reply boundary")
    let .ok crashed := applyEvent replayStart (.crash 0) paused
      | throw (IO.userError "Could not crash before the empty acknowledgement")
    let .ok cuts := prefixes 2000 replayStart 1 crashed
      | throw (IO.userError "Could not enumerate the sibling's publication")
    -- The sibling has enqueued the parent; pause before its acknowledgement.
    let some sibling := cuts.find? fun state =>
        match state.workers 1 with
        | .waiting operation _ => hasMessage Location.root state.durable &&
            retained (Location.root.child 1) 1 state.durable &&
            !retained (Location.root.child 1) 1 (operation state.durable).2
        | _ => false
      | throw (IO.userError "Missing sibling handoff boundary")
    let .ok restarted := Simulation.run replayStart SimulationBackend.advance
        [.advanceTime 10, .restart 0] sibling
      | throw (IO.userError "Could not redeliver the crashed child's work")
    let .ok retries := prefixes 2000 replayStart 0 restarted
      | throw (IO.userError "Could not enumerate the retried response")
    let parentCount := fun state : Durable => state.transport.messages.toList.countP
      (fun message => message.any (·.value == Location.root))
    let some changed := retries.find? fun state =>
        match state.workers 0 with
        | .waiting operation _ => retained (Location.root.child 0) 0 state.durable &&
            parentCount (operation state.durable).2 > parentCount state.durable
        | _ => false
      | throw (IO.userError "Retry did not change the empty response into a parent enqueue")
    let some (some delivery) := changed.durable.transport.messages[0]?
      | throw (IO.userError "Retried child has no delivery")
    assertEq delivery.generation 2 "Retry did not acquire a fresh receipt"
    for loseReply in [false, true] do
      let .ok boundary := if loseReply then applyEvent replayStart (.commit 0) changed else .ok changed
        | throw (IO.userError "Could not commit the retried parent enqueue")
      let .ok interrupted := applyEvent replayStart (.crash 0) boundary
        | throw (IO.userError "Could not interrupt the changed response")
      let .ok expired := applyEvent replayStart (.advanceTime 10) interrupted
        | throw (IO.userError "Could not expire the interrupted retry")
      let .ok finished := drive 20000 replayStart expired 29
        | throw (IO.userError "Replay failed after changing the response")
      Simulated.checkFinished finished (.ok 33)⟩
]

def cases : Array TestCase := generatedCases ++ boundaryCases ++ replayCases ++ changingResponseCases

end LeanCloudTests.ConcurrentPublication
