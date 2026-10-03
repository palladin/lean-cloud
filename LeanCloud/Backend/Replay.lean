import LeanCloud.Backend.Execution
import LeanCloud.ReplayInterpreter
import LeanCloud.CompletionStore
import LeanCloud.LeaseQueue

/-! The public replay interpreter over the common service model. All journal,
completion-record and publish-before-acknowledgement code is shared with Worker.
Infrastructure failure is outside the CloudError channel. -/

namespace LeanCloud.Backend.Replay

abbrev M := ExceptT String Backend.M
abbrev Worker := LeaseQueue.Worker Unit Receipt

def rawDb : LeanCloud.Db Unit M where
  get key handle := do
    let value ← liftM (request (.get key))
    return (value, handle)
  put key value handle := do
    let accepted ← liftM (request (.put key value))
    return (accepted, handle)

def transport : LeanCloud.LeaseQueue Unit M Receipt where
  enqueue location handle := do
    liftM (request (.enqueue location))
    return ((), handle)
  dequeue handle := do
    let delivery ← liftM (request .dequeue)
    return (delivery, handle)
  acknowledge receipt handle := do
    let accepted ← liftM (request (.acknowledge receipt))
    return (accepted, handle)

def db : LeanCloud.Db Worker M := LeaseQueue.db (JournalDb.ofDb rawDb)

def queue : LeanCloud.WorkQueue Worker M :=
  transport.toWorkQueue (CompletionStore.read rawDb throw) (CompletionStore.write rawDb throw)

def noBlobs : BlobStorage Worker M where
  putBlob _ := throw ⟨.unsupported, "Blob operations are outside the pure backend model"⟩
  readBlob _ := throw ⟨.unsupported, "Blob operations are outside the pure backend model"⟩
  resolveBlob _ := throw ⟨.unsupported, "Blob operations are outside the pure backend model"⟩

def initial : Backend.State :=
  { queue.messages := #[{ location := Location.root }] }

def attempt [Codec α] (fuel : Nat) (program : ι → Cloud M α) (input : ι) :
    Backend.M (Except String (Except CloudError α × Worker)) :=
  ((LeanCloud.interpret db noBlobs queue fuel program input).run ⟨(), none⟩).run

end LeanCloud.Backend.Replay
