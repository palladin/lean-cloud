import LeanCloud.Program
import LeanCloudRuntime.Pool

namespace LeanCloudRuntime
open Lean LeanCloud

/-- Existential packaging retains each entry's own input and result codecs. -/
structure RegisteredProgram where
  info : ProgramInfo
  validate : Json → Except String Unit
  worker : Config → String → RunDefinition → IO Unit
  execute : RunDefinition → String → Worker.ObservedStore IO → BlobStorage IO → Trace.Sink → Assignment → IO Report

def registerProgram [Codec ι] [Codec α] (program : LeanCloud.CloudProgram ι α) : RegisteredProgram where
  info := program.info
  validate input := (Codec.decode (α := ι) input).map (fun _ => ())
  worker config run definition := do
    unless definition.entry == program.info.entry && definition.resultSchema == program.info.resultSchema do
      throw (IO.userError "Worker program version or result codec does not match the submitted run")
    let input ← IO.ofExcept (Codec.decode (α := ι) definition.input)
    runWorker config run program.run input
  execute definition worker records blobs trace assignment := do
    unless definition.entry == program.info.entry && definition.resultSchema == program.info.resultSchema do
      throw (IO.userError "Deployed program/codec does not match the submitted run")
    let input ← IO.ofExcept (Codec.decode (α := ι) definition.input)
    Worker.execute worker records blobs 100000
      (fun input => trace.instrument 100000 (program.run input)) input assignment

structure Registry where
  programs : Array RegisteredProgram

def Registry.find (registry : Registry) (entry : String) : Except String RegisteredProgram := do
  let found := registry.programs.filter (·.info.entry == entry)
  match found.toList with
  | [program] => return program
  | [] => throw s!"Unknown program: {entry}"
  | _ => throw s!"Duplicate program entry: {entry}"

def Registry.validate (registry : Registry) : Except String Unit := do
  for program in registry.programs do
    unless !program.info.entry.isEmpty do throw "Program entry cannot be empty"
    discard (registry.find program.info.entry)
    if let some source := program.info.source then
      unless !source.text.isEmpty do throw "Bundled source is empty"
      for site in source.sites do
        unless 0 < site.line && site.line ≤ (source.text.splitOn "\n").length do
          throw "Source location is outside the bundled file"
        unless (source.sites.filter (·.operation == site.operation)).size == 1 do
          throw "Ambiguous source location for operation"

/-- Validate before creating a durable run, including all entry/version checks. -/
def Registry.submit (registry : Registry) (config : Config) (run entry : String) (input : Json) : IO Unit := do
  IO.ofExcept registry.validate
  let program ← IO.ofExcept (registry.find entry)
  IO.ofExcept (program.validate input)
  LeanCloudRuntime.submit config run ⟨entry, input, program.info.resultSchema⟩

def Registry.runWorker (registry : Registry) (config : Config) (run : String) : IO Unit := do
  let definition ← loadRun config run
  let program ← IO.ofExcept (registry.find definition.entry)
  program.worker config run definition

/-- A persistent worker executes one assignment at a time, selecting the entry
from the deployed registry. IO failures escape CloudError and trigger broker
redelivery. Administrative revocation is cooperative at record boundaries. -/
def Registry.serveWorker (registry : Registry) (config : Config) : IO Unit := do
  let id ← workerId
  let broker ← IO.ofExcept (config.mailboxes.worker id)
  let handle ← RabbitMQ.openMailbox broker Pool.address ("worker." ++ id)
  try
    let inbox : Mailbox IO LeanCloud.Pool.Reply := RabbitMQ.inbox handle
    let send (message : LeanCloud.Pool.Message) :=
      Pool.send config message
    let mut nextReady := 0
    IO.println s!"worker {id} ready for deployed programs"
    (← IO.getStdout).flush
    repeat
      if (← IO.monoMsNow) ≥ nextReady then
        send (.ready id)
        nextReady := (← IO.monoMsNow) + 2000
      let some delivery ← inbox.receive | continue
      match delivery.message with
      | .execute run assignment =>
        let revoked ← IO.mkRef false
        let check : IO Unit := do
          let allowed : Bool ← IO.ofExcept (fromJson? (← Pool.request config (.check run id assignment.attempt)))
          unless allowed do
            revoked.set true
            throw (IO.userError "Assignment revoked")
        let trace ← Trace.create id run
        try
          check
          trace.assign assignment
          let report ← if (← completed config run).isSome then
              pure (Report.mk id assignment.attempt (.ok .done) #[])
            else do
              let definition ← loadRun config run
              let program ← IO.ofExcept (registry.find definition.entry)
              let records := trace.records (S3.records config.blobs run)
              let guarded : ReplayStore IO := {
                read := fun key => do check; records.read key
                create := fun key value => do check; records.create key value }
              let observed ← observe guarded
              program.execute definition id observed (trace.blobs (S3.storage config.blobs)) trace assignment
          trace.emit (match report.progress with | .ok (.fork ..) => "suspended" | .ok .done => "returned" | .error _ => "failed") ""
          send (.report run report)
        catch error =>
          if ← revoked.get then trace.emit "revoked" "" else throw error
        trace.emit "idle" ""
        -- Confirm readiness before ack. A crash can duplicate assignments; the
        -- coordinator and immutable records tolerate that redelivery.
        send (.ready id)
        nextReady := (← IO.monoMsNow) + 2000
      | .drain generation => send (.drained id generation)
      | .idle | .acknowledged => pure ()
      inbox.acknowledge delivery.receipt
  finally handle.close

/-- A typed handle can inspect the durable result without a live scheduler. -/
structure CloudProcess (α : Type) [Codec α] where
  config : Config
  id : String
  entry : String

def submitProgram [Codec ι] [Codec α] (program : LeanCloud.CloudProgram ι α)
    (config : Config) (id : String) (input : ι) : IO (CloudProcess α) := do
  Registry.submit ⟨#[registerProgram program]⟩ config id program.info.entry (Codec.encode input)
  Pool.submit config id
  return ⟨config, id, program.info.entry⟩

def CloudProcess.poll [Codec α] (process : CloudProcess α) : IO (Option (Except CloudError α)) := do
  let definition ← loadRun process.config process.id
  unless definition.entry == process.entry && definition.resultSchema == (inferInstance : Codec α).schema do
    throw (IO.userError "Process handle does not match the submitted program/result codec")
  let some outcome ← completed process.config process.id | return none
  return some ((ReplayInterpreter.result (m := Id) outcome).run)

def CloudProcess.await [Codec α] (process : CloudProcess α) (pollMs : UInt32 := 500) :
    IO (Except CloudError α) := do
  repeat
    if let some result ← process.poll then return result
    IO.sleep (max 1 pollMs)

end LeanCloudRuntime

namespace LeanCloud.CloudProgram

def register [Codec ι] [Codec α] (program : CloudProgram ι α) :=
  LeanCloudRuntime.registerProgram program

/-- Typed submission to the persistent pool. Confirmed registration survives scheduler downtime. -/
def submit [Codec ι] [Codec α] (program : CloudProgram ι α)
    (config : LeanCloudRuntime.Config) (id : String) (input : ι) :=
  LeanCloudRuntime.submitProgram program config id input

end LeanCloud.CloudProgram
