import LeanCloudTests.Recovery
import LeanCloud.Backend.Replay
import LeanCloud.Backend.Check

namespace LeanCloudTests.BackendContracts
open Lean LeanCloud Backend

private def apply (decision : Decision) (operation : Request α) (state : Backend.State) :
    IO (α × Backend.State) := IO.ofExcept (execute decision operation state)

private def runEvents (programs : Array (Backend.M α)) (events : List Execution.Event)
    (state : Execution.State α) : Except String (Execution.State α) :=
  Execution.run programs events state

private def primitiveCases : Array TestCase := #[
  ⟨"backend-contract/checker-rejects-stale-read", do
    let states ← IO.ofExcept (Backend.Check.observe (.put "a" (toJson (17 : Nat))) true #[{}])
    assertTrue (match Backend.Check.observe (.get "a") none states with | .error _ => true | .ok _ => false)
      "Checker accepted a fresh read missing a committed write"⟩,
  ⟨"backend-contract/checker-rejects-invented-delivery", do
    assertTrue (match Backend.Check.observe .dequeue (some (Location.root, 0)) #[{}] with | .error _ => true | .ok _ => false)
      "Checker accepted a delivery without a publication"⟩,
  ⟨"backend-contract/checker-keeps-ambiguous-publications", do
    let states ← IO.ofExcept (Backend.Check.observe (.enqueue Location.root) () #[{}])
    let states ← IO.ofExcept (Backend.Check.observe (.enqueue Location.root) () states)
    let states ← IO.ofExcept (Backend.Check.observe .dequeue (some (Location.root, 0)) states)
    assertEq states.size 2
    let states ← IO.ofExcept (Backend.Check.observe (.acknowledge 0) true states)
    assertEq states.size 2⟩,
  ⟨"backend-contract/acknowledged-publication-can-be-redelivered", do
    let (_, state) ← apply {} (.enqueue Location.root) {}
    let (first, state) ← apply ⟨some 0, true⟩ .dequeue state
    assertEq first (some (Location.root, 0))
    let (accepted, state) ← apply {} (.acknowledge 0) state
    assertEq accepted true
    let (second, state) ← apply ⟨some 0, true⟩ .dequeue state
    assertEq second (some (Location.root, 1))
    assertEq state.queue.messages.size 1
    assertEq state.queue.messages[0]!.acknowledged true⟩,
  ⟨"backend-contract/stale-receipt-may-be-accepted", do
    let (_, state) ← apply {} (.enqueue Location.root) {}
    let (_, state) ← apply ⟨some 0, true⟩ .dequeue state
    let (_, state) ← apply ⟨some 0, true⟩ .dequeue state
    let (accepted, _) ← apply {} (.acknowledge 0) state
    assertEq accepted true⟩,
  ⟨"backend-contract/idle-and-out-of-order-delivery", do
    let (_, state) ← apply {} (.enqueue Location.root) {}
    let (_, state) ← apply {} (.enqueue Location.root.next) state
    let (idle, unchanged) ← apply {} .dequeue state
    assertEq idle none
    assertEq unchanged state
    let (second, _) ← apply ⟨some 1, true⟩ .dequeue state
    assertEq second (some (Location.root.next, 0))⟩,
  ⟨"backend-contract/acknowledgement-does-not-settle-another-publication", do
    let (_, state) ← apply {} (.enqueue Location.root) {}
    let (_, state) ← apply {} (.enqueue Location.root) state
    let (_, state) ← apply ⟨some 1, true⟩ .dequeue state
    let (_, state) ← apply {} (.acknowledge 0) state
    assertEq state.queue.messages[0]!.acknowledged false
    assertEq state.queue.messages[1]!.acknowledged true⟩,
  ⟨"backend-contract/rejected-acknowledgement-keeps-obligation", do
    let (_, state) ← apply {} (.enqueue Location.root) {}
    let (_, state) ← apply ⟨some 0, true⟩ .dequeue state
    let (accepted, after) ← apply ⟨none, false⟩ (.acknowledge 0) state
    assertEq accepted false
    assertEq after state⟩,
  ⟨"backend-contract/fresh-read-sees-committed-write", do
    let (_, state) ← apply {} (.put "a" (toJson (17 : Nat))) {}
    let (_, state) ← apply {} (.put "b" (toJson (31 : Nat))) state
    let (value, _) ← apply {} (.get "a") state
    assertEq value (some (toJson (17 : Nat)))⟩,
  ⟨"backend-contract/request-can-commit-after-crash-and-replacement", do
    let programs : Array (Backend.M Bool) := #[request (.put "value" (toJson (7 : Nat)))]
    let start := Execution.initial {} programs
    let .ok state := runEvents programs [.crash 0, .restart 0, .commit 0] start
      | throw (IO.userError "Late commit schedule failed")
    assertEq (Backend.Db.view state.services "value") (some (toJson (7 : Nat)))
    -- The old reply must not resume the replacement's continuation.
    let .ok state := runEvents programs [.reply 0] state
      | throw (IO.userError "Old reply schedule failed")
    match state.workers[0]?.map (·.status) with
    | some (.waiting 1) => pure ()
    | _ => throw (IO.userError "Old reply resumed the replacement")
    let .ok state := runEvents programs [.commit 1, .reply 1] state
      | throw (IO.userError "Replacement schedule failed")
    match state.workers[0]?.map (·.status) with
    | some (.finished true) => pure ()
    | _ => throw (IO.userError "Replacement did not finish")⟩,
  ⟨"backend-contract/reply-lost-after-commit", do
    let programs : Array (Backend.M Bool) := #[request (.put "value" (toJson (7 : Nat)))]
    let .ok state := runEvents programs [.commit 0, .crash 0, .reply 0, .restart 0]
      (Execution.initial {} programs)
      | throw (IO.userError "Lost reply schedule failed")
    assertEq (Backend.Db.view state.services "value") (some (toJson (7 : Nat)))
    match state.workers[0]?.map (·.status) with
    | some (.waiting 1) => pure ()
    | _ => throw (IO.userError "Lost reply changed the new attempt")⟩
]

private def nextSeed (seed : Nat) : Nat := (seed * 1664525 + 1013904223) % 4294967296

private def decision (seed : Nat) (state : Backend.State) : Decision :=
  let pending := (List.range state.queue.messages.size).filter fun id =>
    state.queue.messages[id]?.any (! ·.acknowledged)
  -- Most polls advance unsettled work; some revisit acknowledged publications.
  let candidates := if seed % 7 == 0 then List.range state.queue.messages.size else pending
  { delivery := if seed % 13 == 0 then none else candidates[seed % max 1 candidates.length]?
    acceptAcknowledgement := seed % 11 != 0 }

private def actions (seed : Nat) (crashes : Bool) (state : Execution.State α) : Array Execution.Event := Id.run do
  let mut events := #[]
  for id in [:state.calls.size] do
    match state.calls[id]? with
    | some (.pending ..) => events := events.push (.commit id (decision seed state.services))
    | some (.committed ..) => events := events.push (.reply id)
    | _ => pure ()
  for id in [:state.workers.size] do
    match (state.workers[id]?).map (fun worker => worker.status) with
    | some (Execution.Status.stopped) => events := events.push (.restart id)
    | some (Execution.Status.waiting _) => if crashes then events := events.push (.crash id)
    | _ => pure ()
  return events

private def allReturned (state : Execution.State α) : Bool :=
  !state.workers.isEmpty && state.workers.all fun worker =>
    match worker.status with
    | .finished _ => true
    | _ => false

private def drive (programs : Array (Backend.M α)) (seed : Nat) (crashSteps : Nat)
    (state : Execution.State α) : Nat → Except String (Array α × Backend.State)
  | 0 => throw "Backend-model schedule exhausted"
  | left + 1 => do
    if allReturned state then
      let results := state.workers.filterMap fun worker =>
        match worker.status with | .finished value => some value | _ => none
      return (results, state.services)
    let seed := nextSeed seed
    let enabled := actions seed (crashSteps > 0) state
    let some event := enabled[seed % max 1 enabled.size]?
      | throw "Backend-model execution has no enabled action"
    match runEvents programs [event] state with
    | .error error => throw error
    | .ok after => drive programs seed (crashSteps - 1) after left

def runReplay (program : Nat → Cloud Backend.Replay.M Nat) (input seed : Nat) :
    IO (Except CloudError Nat × Backend.State) := do
  let workers := Array.replicate 3 (Backend.Replay.attempt 10000 program input)
  let (results, final) ← IO.ofExcept (drive workers seed 60 (Execution.initial Backend.Replay.initial workers) 30000)
  let some result := results[0]?
    | throw (IO.userError "Backend-model execution has no worker")
  let actual ← IO.ofExcept result
  assertEq results.size workers.size
  for result in results do
    let (outcome, handle) ← IO.ofExcept result
    assertOutcome outcome actual.1
    assertTrue handle.delivery.isNone "A returned worker retained its lease receipt"
  return (actual.1, final)

private def differential (seed : Nat) : IO Unit := do
  let tree := (generate 3 (seed + 1)).1
  let program : Nat → Cloud Backend.Replay.M Nat := RecoveryTests.lowerPure tree
  let input := seed % 13
  let direct := ((DirectInterpreter.interpret Backend.Replay.noBlobs program input).run ⟨(), none⟩).run
  let expected ← match direct with
    | .pure (.ok (outcome, _)) => pure outcome
    | _ => throw (IO.userError "Pure direct interpreter issued a service operation")
  let (actual, final) ← runReplay program input seed
  assertOutcome actual expected
  let encoded := match expected with
    | .ok value => Exit.success (Codec.encode value)
    | .error error => Exit.failure error
  assertEq (Backend.Db.view final CompletionStore.key) (some (toJson encoded))

def cases : Array TestCase := primitiveCases ++ (Array.range 48).map fun seed =>
  ⟨s!"backend-contract/differential-{seed}", differential seed⟩

end LeanCloudTests.BackendContracts
