import LeanCloud.Simulation
import LeanCloud.ReplayInterpreter
import LeanCloud.JournalDb
import LeanCloud.LeaseQueue
import LeanCloud.LeaseQueueModel

/-! The actual replay interpreter over a shared simulated journal and leased
queue. Each physical operation issues one request; adapters retain their normal
multi-operation behavior. Time and crashes belong to the external driver. -/

namespace LeanCloud.SimulationBackend
open Lean

structure Durable where
  /-- Newest writes first. Keeping the log exposes chronology to the proofs;
  `lookup` still implements the ordinary key/value interface. -/
  records : List (String × Json) := []
  transport : LeaseQueueModel.State Location := {}
  completed : Option Exit := none
  deriving Repr, BEq

abbrev M := SimM Durable
abbrev Worker := LeaseQueue.Worker Unit LeaseQueueModel.Receipt

def rawDb : Db Unit M where
  get key handle := do
    let value ← SimM.atomic fun state => (state.records.lookup key, state)
    return (value, handle)
  put key value handle := do
    let result ← SimM.atomic fun state =>
      (true, { state with records := (key, value) :: state.records })
    return (result, handle)

def db : Db Worker M := LeaseQueue.db (JournalDb.ofDb rawDb)

def transport (leaseDuration : Nat) : LeaseQueue Unit M LeaseQueueModel.Receipt where
  enqueue location handle := do
    let _ ← SimM.atomic fun state =>
      let (_, transport) := LeaseQueueModel.enqueue location state.transport
      ((), { state with transport })
    return ((), handle)
  dequeue handle := do
    let delivery ← SimM.atomic fun state =>
      let (delivery, transport) := LeaseQueueModel.dequeue leaseDuration state.transport
      (delivery.map (fun d => (d.value, d.receipt)), { state with transport })
    return (delivery, handle)
  acknowledge receipt handle := do
    let accepted ← SimM.atomic fun state =>
      let (accepted, transport) := LeaseQueueModel.acknowledge receipt state.transport
      (accepted, { state with transport })
    return (accepted, handle)

def readCompleted : StateT Unit M (Option Exit) := fun handle => do
  return (← SimM.atomic (fun state => (state.completed, state)), handle)

def writeCompleted (outcome : Exit) : StateT Unit M Unit := fun handle => do
  let _ ← SimM.atomic fun state => ((), { state with completed := some outcome })
  return ((), handle)

def queue (leaseDuration : Nat) : WorkQueue Worker M :=
  (transport leaseDuration).toWorkQueue readCompleted writeCompleted

/-- This backend models the pure workflow fragment; blob actions are explicit
errors. Arbitrary IO actions are not translated into simulated operations. -/
def noBlobs : BlobStorage Worker M where
  putBlob _ := throw ⟨.unsupported, "Blob operations are not modeled by this simulation"⟩
  readBlob _ := throw ⟨.unsupported, "Blob operations are not modeled by this simulation"⟩
  resolveBlob _ := throw ⟨.unsupported, "Blob operations are not modeled by this simulation"⟩

def initial : Durable :=
  { transport := (LeaseQueueModel.enqueue Location.root {}).2 }

def advance (elapsed : Nat) (state : Durable) : Durable :=
  { state with transport := LeaseQueueModel.advance elapsed state.transport }

/-- Restart this value with fresh local state. The scheduler owns durable state,
so reconstructing an attempt neither clears records nor seeds another root. -/
def attempt [Codec α] (fuel leaseDuration : Nat)
    (program : ι → Cloud M α) (input : ι) : M (Except CloudError α × Worker) :=
  (interpret db noBlobs (queue leaseDuration) fuel program input).run ⟨(), none⟩

end LeanCloud.SimulationBackend
