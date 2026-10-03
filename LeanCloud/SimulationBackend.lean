import LeanCloud.Simulation
import LeanCloud.Worker
import LeanCloud.MailboxModel

/-! The scheduler and workers use their production actor turns and interpreter.
Only their ports differ. Mailbox delivery, process scheduling and crashes remain
external choices; the shared world is a model, not a service deployed in production. -/

namespace LeanCloud.SimulationBackend
open Lean

inductive Envelope where
  | scheduler (message : SchedulerMessage)
  | worker (delivery : Delivery)
  deriving Repr

structure World where
  scheduler : Scheduler.State := {}
  records : List (String × ReplayRecord) := []
  blobs : List (String × ByteArray) := []
  names : List (String × BlobRef) := []
  network : Array Envelope := #[]
  schedulerInbox : MailboxModel.Inbox SchedulerMessage := {}
  workerInboxes : List (WorkerId × MailboxModel.Inbox WorkerMessage) := []
  observations : List (WorkerId × Array String) := []
  writes : Nat := 0
  reads : Nat := 0

private def setEntry [BEq κ] (entries : List (κ × ν)) (key : κ) (value : ν) : List (κ × ν) :=
  (key, value) :: entries.filter (fun entry => entry.1 != key)

/-- Atomic create-if-absent, shared by all simulated workers. -/
def create (key : String) (record : ReplayRecord) (world : World) : ReplayRecord × World :=
  match world.records.lookup key with
  | some existing => (existing, world)
  | none => (record, { world with records := (key, record) :: world.records, writes := world.writes + 1 })

def records : ReplayStore (SimM World) where
  read key := SimM.atomic (fun world =>
    (world.records.lookup key, { world with reads := world.reads + 1 })) s!"record.read:{key}"
  create key record := SimM.atomic (create key record) s!"record.create:{key}"

private def note (worker : WorkerId) (key : String) : SimM World Unit :=
  SimM.local (fun world =>
    let keys := (world.observations.lookup worker).getD #[]
    let keys := if keys.contains key then keys else keys.push key
    ((), { world with observations := setEntry world.observations worker keys })) "worker.observe"

def observed (worker : WorkerId) : Worker.ObservedStore (SimM World) where
  records := {
    read := fun key => do
      let record ← records.read key
      if record.isSome then note worker key
      return record
    create := fun key record => do
      let record ← records.create key record
      note worker key
      return record }
  confirmed := SimM.local (fun world => ((world.observations.lookup worker).getD #[], world))
    "worker.confirmed"

def blobs : BlobStorage (SimM World) where
  putBlob bytes := liftM (m := SimM World) <| SimM.atomic (fun world =>
    let key := s!"blob/{modelChecksum bytes}/{bytes.size}"
    let ref := { key, size := bytes.size, checksum := modelChecksum bytes : BlobRef }
    (ref, { world with blobs := setEntry world.blobs key bytes })) "blob.put"
  readBlob ref := do
    let bytes ← liftM (m := SimM World) <| SimM.atomic (fun world => (world.blobs.lookup ref.key, world)) "blob.read"
    let some bytes := bytes | throw ⟨.missingBlob, "Missing blob"⟩
    unless bytes.size == ref.size && modelChecksum bytes == ref.checksum do
      throw ⟨.integrity, "Invalid blob reference"⟩
    return bytes
  resolveBlob name := do
    let ref ← liftM (m := SimM World) <| SimM.atomic (fun world => (world.names.lookup name, world)) "blob.resolve"
    let some ref := ref | throw ⟨.missingBlob, "Missing blob name"⟩
    return ref

def schedulerPorts (generation : Nat) : SchedulerPorts (SimM World) where
  inbox.receive := SimM.atomic (fun world =>
    let (delivery, inbox) := MailboxModel.receive generation world.schedulerInbox
    (delivery, { world with schedulerInbox := inbox })) "scheduler.receive"
  inbox.acknowledge receipt := SimM.atomic (fun world =>
    ((), { world with schedulerInbox := MailboxModel.acknowledge generation receipt world.schedulerInbox }))
    "scheduler.acknowledge"
  localDb.load := SimM.local (fun world => (world.scheduler, world)) "scheduler.load"
  localDb.save state := SimM.local (fun world => ((), { world with scheduler := state })) "scheduler.save"
  send delivery := SimM.atomic (fun world =>
    ((), { world with network := world.network.push (.worker delivery) })) "scheduler.send"

def workerPorts (id : WorkerId) (generation : Nat) : Worker.Ports (SimM World) where
  id
  inbox.receive := SimM.atomic (fun world =>
    let (delivery, inbox) := MailboxModel.receive generation ((world.workerInboxes.lookup id).getD {})
    (delivery, { world with workerInboxes := setEntry world.workerInboxes id inbox })) "worker.receive"
  inbox.acknowledge receipt := SimM.atomic (fun world =>
    let inbox := MailboxModel.acknowledge generation receipt ((world.workerInboxes.lookup id).getD {})
    ((), { world with workerInboxes := setEntry world.workerInboxes id inbox })) "worker.acknowledge"
  send message := SimM.atomic (fun world =>
    ((), { world with network := world.network.push (.scheduler message) })) "worker.send"
  observe := observed id
  blobs

/-- Each actor has a finite run budget. Exhaustion pauses the simulation; it is
not evidence of workflow completion. Restart gives a fresh volatile continuation. -/
def schedulerLoop (turns duration generation : Nat) : SimM World Unit :=
  match turns with
  | 0 => pure ()
  | turns + 1 => do
    Scheduler.turn (schedulerPorts generation) duration
    schedulerLoop turns duration generation

def workerLoop [Codec α] (turns fuel : Nat) (ports : Worker.Ports (SimM World))
    (program : ι → Cloud (SimM World) α) (input : ι) (state : Worker.State := {}) : SimM World Unit :=
  match turns with
  | 0 => pure ()
  | turns + 1 => do
    let state ← Worker.turn ports fuel program input state
    if !state.stopped then workerLoop turns fuel ports program input state

/-- Actor zero is the scheduler; all remaining actors are workers. -/
def start [Codec α] (turns fuel duration : Nat)
    (program : ι → Cloud (SimM World) α) (input : ι) : Simulation.Start World Unit (workers + 1) :=
  fun actor generation => do
    if actor.val == 0 then
      SimM.atomic (fun world => ((), { world with
        schedulerInbox := MailboxModel.connect generation world.schedulerInbox })) "scheduler.connect"
      Scheduler.recover (schedulerPorts generation).localDb
      schedulerLoop turns duration generation
    else
      let id := s!"worker-{actor.val}"
      SimM.atomic (fun world =>
        let inbox := MailboxModel.connect generation ((world.workerInboxes.lookup id).getD {})
        ((), { world with workerInboxes := setEntry world.workerInboxes id inbox })) "worker.connect"
      workerLoop turns fuel (workerPorts id generation) program input

/-- The broker observes consumer failure independently of the actor continuation.
Already confirmed publications survive; old receive/ack requests are session-fenced. -/
def disconnect (actor generation : Nat) (world : World) : World :=
  if actor == 0 then { world with schedulerInbox := MailboxModel.disconnect generation world.schedulerInbox }
  else
    let id := s!"worker-{actor}"
    let inbox := MailboxModel.disconnect generation ((world.workerInboxes.lookup id).getD {})
    { world with
      workerInboxes := setEntry world.workerInboxes id inbox
      observations := world.observations.filter (fun entry => entry.1 != id) }

def step (start : Simulation.Start World α count) (event : Simulation.Event count)
    (state : Simulation.State World α count) : Except Simulation.Error (Simulation.State World α count) := do
  let next ← Simulation.step start event state
  match event with
  | .crash actor => return { next with world := disconnect actor.val (state.generations actor) next.world }
  | _ => return next

/-- Publication confirmation puts a message in durable broker state. Delivery can
be delayed or duplicated, but a confirmed message cannot simply be dropped. -/
inductive NetworkEvent where
  | deliver (index : Nat)
  | duplicate (index : Nat)
  | hold
  | tick (elapsed : Nat)
  deriving Repr, BEq

def networkStep (event : NetworkEvent) (world : World) : World := Id.run do
  match event with
  | .tick elapsed =>
    let inbox := MailboxModel.publish (.tick elapsed) world.schedulerInbox
    return { world with schedulerInbox := inbox }
  | .hold => return world
  | .duplicate index =>
    let some envelope := world.network[index]? | return world
    return { world with network := world.network.push envelope }
  | .deliver index =>
    let some envelope := world.network[index]? | return world
    let world := { world with network := world.network.eraseIdxIfInBounds index }
    match envelope with
    | .scheduler message => return { world with schedulerInbox := MailboxModel.publish message world.schedulerInbox }
    | .worker delivery =>
      let inbox := (world.workerInboxes.lookup delivery.worker).getD {}
      let inboxes := setEntry world.workerInboxes delivery.worker (MailboxModel.publish delivery.message inbox)
      return { world with workerInboxes := inboxes }

end LeanCloud.SimulationBackend
