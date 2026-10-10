import LeanCloud.Scheduler

namespace LeanCloud

/-- A receipt belongs to this inbox's current consumer session. -/
structure Received (message : Type) where
  receipt : Nat
  message : message

/-- A durable actor inbox, with one unacknowledged delivery at a time. Receiving
reserves a message; only acknowledgement removes it. On consumer failure it is
redelivered. Receipt identities are scoped to this mailbox session. Outgoing
`send` operations return only after the mailbox service confirms durable publication. -/
structure Mailbox (m : Type → Type u) (message : Type) where
  receive : m (Option (Received message))
  acknowledge : Nat → m Unit

/-- Process-owned scheduling state. Saving must durably commit its catalog;
the recursive continuation remains in memory only. -/
structure SchedulerStore (m : Type → Type u) where
  load : m Scheduler.State
  save : Scheduler.State → m Unit

structure SchedulerPorts (m : Type → Type u) where
  inbox : Mailbox m SchedulerMessage
  localDb : SchedulerStore m
  send : Delivery → m Unit

/-- On startup, cancel every known worker before rebuilding from the root.
Attempt counters survive; replay records reconstruct completed work. -/
def Scheduler.recover [Monad m] (store : SchedulerStore m) : m Unit := do
  let state ← store.load
  store.save (Scheduler.cancel state (state.workers.map (·.worker)))

/-- Commit the catalog first, confirm outgoing messages next, acknowledge input
last. Redelivery is harmless; process recovery discards the old traversal. -/
def Scheduler.turn [Monad m] (ports : SchedulerPorts m) (duration : Nat) : m Unit := do
  let some delivery ← ports.inbox.receive | return
  let state ← ports.localDb.load
  let (state, outgoing) := Scheduler.handle duration state delivery.message
  ports.localDb.save state
  for message in outgoing do ports.send message
  ports.inbox.acknowledge delivery.receipt

end LeanCloud
