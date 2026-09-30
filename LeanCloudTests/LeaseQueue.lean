import LeanCloudTests.SimulationSupport

namespace LeanCloudTests.Leases
open LeanCloud LeanCloud.LeaseQueueModel

def required (value : Option α) : IO α :=
  match value with
  | some value => pure value
  | none => throw (IO.userError "Expected a delivery")

def seed : State Location := (enqueue Location.root {}).2

def cases : Array TestCase := #[
  ⟨"lease/empty-poll", do
    let state : State Location := {}
    assertEq (dequeue 5 state) (none, state)⟩,
  ⟨"lease/dequeue-retains-and-hides", do
    let (result, state) := dequeue 5 seed
    let delivery ← required result
    assertEq delivery.value Location.root
    assertEq delivery.visibleAt 5
    assertEq state.messages.size 1
    assertTrue state.messages[0]!.isSome "Dequeue removed the message"
    assertEq (dequeue 5 state) (none, state)⟩,
  ⟨"lease/expiry-and-new-receipt", do
    let (first, state) := dequeue 5 seed
    let first ← required first
    let state := advance 4 state
    assertEq (dequeue 5 state).1 none
    let (second, state) := dequeue 5 (advance 1 state)
    let second ← required second
    assertEq second.value first.value
    assertTrue (second.receipt != first.receipt) "Redelivery reused the receipt"
    assertEq (acknowledge first.receipt state) (false, state)
    let (accepted, state) := acknowledge second.receipt state
    assertTrue accepted "Current receipt rejected"
    assertEq (dequeue 5 (advance 100 state)).1 none⟩,
  ⟨"lease/skips-hidden-message", do
    let state := (enqueue Location.root.next seed).2
    let (first, state) := dequeue 5 state
    let first ← required first
    let (second, state) := dequeue 5 state
    let second ← required second
    assertEq first.value Location.root
    assertEq second.value Location.root.next
    assertEq (dequeue 5 state).1 none
    let (_, state) := acknowledge first.receipt state
    assertTrue (current second.receipt state).isSome "Ack removed another worker's message"⟩,
  ⟨"lease/duplicate-payloads-are-separate", do
    let state := (enqueue Location.root seed).2
    let (first, state) := dequeue 5 state
    let first ← required first
    let (second, state) := dequeue 5 state
    let second ← required second
    assertEq first.value second.value
    assertTrue (first.receipt.message != second.receipt.message) "Enqueue deduplicated work"
    let (_, state) := acknowledge first.receipt state
    assertTrue (current second.receipt state).isSome "Ack matched the payload instead of the receipt"⟩,
  ⟨"lease/renewal-rotates-receipt", do
    let (first, state) := dequeue 5 seed
    let first ← required first
    let (renewed, state) := renew first.receipt 10 (advance 2 state)
    let renewed ← required renewed
    assertEq renewed.visibleAt 12
    assertEq renewed.value first.value
    assertTrue (renewed.receipt != first.receipt) "Renewal reused the old receipt"
    assertEq (acknowledge first.receipt state) (false, state)
    assertEq (renew first.receipt 20 state) (none, state)
    assertEq (dequeue 5 (advance 9 state)).1 none
    assertTrue (dequeue 5 (advance 10 state)).1.isSome "Renewed lease never expired"⟩,
  ⟨"lease/expiry-without-redelivery-allows-ack", do
    let (delivery, state) := dequeue 5 seed
    let delivery ← required delivery
    assertTrue (acknowledge delivery.receipt (advance 5 state)).1
      "Expiry alone invalidated the current receipt"⟩,
  ⟨"lease/zero-duration", do
    let (first, state) := dequeue 0 seed
    let first ← required first
    let (second, _) := dequeue 0 state
    let second ← required second
    assertTrue (second.receipt != first.receipt) "Immediate redelivery reused the receipt"⟩,
  ⟨"lease/invalid-and-repeated-ack", do
    assertEq (acknowledge ⟨0, 0⟩ seed) (false, seed)
    assertEq (acknowledge ⟨99, 1⟩ seed) (false, seed)
    let (delivery, state) := dequeue 5 seed
    let delivery ← required delivery
    let (_, state) := acknowledge delivery.receipt state
    assertEq (acknowledge delivery.receipt state) (false, state)
    let (newId, state) := enqueue Location.root state
    assertTrue (newId != delivery.receipt.message) "Deleted message id was reused"
    assertEq (acknowledge delivery.receipt state) (false, state)⟩,
  ⟨"lease/crash-before-dequeue", do
    let action := SimM.atomic (dequeue (α := Location) 5)
    let .ok state := SimTest.events action advance [.crash 0] (SimTest.initial action seed)
      | throw (IO.userError "Simulation schedule did not finish")
    assertEq (state.workers 0).phase .stopped
    assertEq state.durable seed⟩,
  ⟨"lease/crash-after-dequeue-does-not-release", do
    let action := SimM.atomic (dequeue (α := Location) 5)
    let .ok state := SimTest.events action advance
      [.commit 0, .crash 0, .restart 0, .commit 0, .resume 0] (SimTest.initial action seed)
      | throw (IO.userError "Simulation schedule did not finish")
    assertEq (← SimTest.value state) none "Restart released the crashed worker's lease"
    assertEq state.durable.now 0 "Restart secretly advanced time"
    let (result, _) ← SimTest.finish action (advance 5 state.durable)
    let delivery ← required result
    assertEq delivery.value Location.root
    assertEq delivery.receipt.generation 2⟩,
  ⟨"lease/crash-around-ack", do
    let (delivery, leased) := dequeue 5 seed
    let delivery ← required delivery
    let action := SimM.atomic (acknowledge (α := Location) delivery.receipt)
    for committed in [false, true] do
      let schedule := (if committed then [Simulation.Event.commit 0] else []) ++ [.crash 0]
      let .ok state := SimTest.events action advance schedule (SimTest.initial action leased)
        | throw (IO.userError "Simulation schedule did not finish")
      assertEq (state.workers 0).phase .stopped
      let (redelivery, _) := dequeue 5 (advance 5 state.durable)
      assertEq redelivery.isSome (!committed)
        "Ack crash retained or removed the wrong message"⟩,
  ⟨"lease/lost-enqueue-reply-can-duplicate", do
    let action := SimM.atomic (enqueue Location.root)
    let .ok state := SimTest.events action advance
      [.commit 0, .crash 0, .restart 0, .commit 0, .resume 0] (SimTest.initial action {})
      | throw (IO.userError "Simulation schedule did not finish")
    assertEq (← SimTest.value state) 1
    assertEq state.durable.messages.size 2 "Retry hid a duplicate enqueue"⟩,
  ⟨"lease/lost-renewal-reply", do
    let (delivery, state) := dequeue 5 seed
    let delivery ← required delivery
    let action := SimM.atomic (renew (α := Location) delivery.receipt 10)
    let .ok state := SimTest.events action advance [.commit 0, .crash 0]
      (SimTest.initial action (advance 2 state))
      | throw (IO.userError "Simulation schedule did not finish")
    assertEq (state.workers 0).phase .stopped
    assertEq (acknowledge delivery.receipt state.durable).1 false
    assertEq (dequeue 5 (advance 3 state.durable)).1 none
    assertTrue (dequeue 5 (advance 10 state.durable)).1.isSome "Lost renewal made work unrecoverable"⟩,
  ⟨"lease/repeated-expiry", do
    let mut state := seed
    let mut receipts : Array Receipt := #[]
    for generation in [1:101] do
      let (delivery, next) := dequeue 3 state
      let delivery ← required delivery
      assertEq delivery.value Location.root
      assertEq delivery.receipt.generation generation
      for old in receipts do
        assertEq (acknowledge old next) (false, next) "Old receipt acknowledged a newer delivery"
      receipts := receipts.push delivery.receipt
      state := advance 3 next
    let receipt ← required receipts[99]?
    let (accepted, finished) := acknowledge receipt state
    assertTrue accepted "Final delivery could not be acknowledged"
    assertEq (dequeue 3 finished).1 none⟩
]

end LeanCloudTests.Leases
