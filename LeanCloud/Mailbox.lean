import LeanCloud.Scheduler

namespace LeanCloud

/-- A receipt belongs to this inbox's current consumer session. -/
structure Received (message : Type) where
  receipt : Nat
  message : message

/-- A durable actor inbox, with one unacknowledged delivery at a time. Receiving
reserves a message; only acknowledgement removes it. On consumer failure it is
redelivered. Receipt identities are scoped to this mailbox session. Outgoing
`send` operations return only after the broker confirms durable publication. -/
structure Mailbox (m : Type → Type u) (message : Type) where
  receive : m (Option (Received message))
  acknowledge : Nat → m Unit

/-- Only the scheduler process accesses its private durable state. -/
structure SchedulerStore (m : Type → Type u) where
  load : m Scheduler.State
  save : Scheduler.State → m Unit

structure SchedulerPorts (m : Type → Type u) where
  inbox : Mailbox m SchedulerMessage
  localDb : SchedulerStore m
  send : Delivery → m Unit

/-- Recover the private database before receiving mail in a fresh process.
Abandoned attempts become pending; completed jobs and partial joins survive.
This does not depend on the old process's clock or assignment timeout. -/
def Scheduler.recover [Monad m] (store : SchedulerStore m) : m Unit := do
  let state ← store.load
  store.save { state with jobs := state.jobs.map fun job =>
    match job.status with
    | .running .. => { job with status := .pending }
    | _ => job }

/-- Persist first, confirm outgoing messages next, acknowledge the input last.
A crash at either boundary causes redelivery; handling duplicates is idempotent. -/
def Scheduler.turn [Monad m] (ports : SchedulerPorts m) (duration : Nat) : m Unit := do
  let some delivery ← ports.inbox.receive | return
  let state ← ports.localDb.load
  let (state, outgoing) := Scheduler.handle duration state delivery.message
  ports.localDb.save state
  for message in outgoing do ports.send message
  ports.inbox.acknowledge delivery.receipt

end LeanCloud
