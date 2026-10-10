import LeanCloud.Program
import LeanCloudRuntime.Pool

namespace LeanCloudRuntime
open Lean LeanCloud

/-- Existential packaging retains each entry's own input and result codecs. -/
structure RegisteredProgram where
  info : ProgramInfo
  validate : Json → Except String Unit
  execute : RunDefinition → String → Worker.ObservedStore IO → BlobStorage IO → Trace.Sink → Assignment → IO Report

def registerProgram [Codec ι] [Codec α] (program : LeanCloud.CloudProgram ι α)
    (sources : Array ProgramSource := by exact cloud_sources%) : RegisteredProgram where
  info := { program.info with sources }
  validate input := (Codec.decode (α := ι) input).map (fun _ => ())
  execute definition worker records blobs trace assignment := do
    unless definition.entry == program.info.entry && definition.resultSchema == program.info.resultSchema do
      throw (IO.userError "Deployed program/codec does not match the submitted run")
    let input ← IO.ofExcept (Codec.decode (α := ι) definition.input)
    Worker.execute worker records blobs 100000
      (fun input => trace.instrument 100000 (program.run input)) input assignment (some trace.visit)

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
    for source in program.info.sources do
      unless !source.text.isEmpty do throw "Bundled source is empty"
      for site in source.sites do
        unless 0 < site.line && site.line ≤ (source.text.splitOn "\n").length do
          throw "Source location is outside the bundled file"
        unless (source.sites.filter (·.id == site.id)).size == 1 do
          throw "Duplicate source site identifier"

/-- Validate before creating a durable run, including all entry/version checks. -/
def Registry.submit (registry : Registry) (config : Config) (run entry : String) (input : Json) : IO Unit := do
  IO.ofExcept registry.validate
  let program ← IO.ofExcept (registry.find entry)
  IO.ofExcept (program.validate input)
  LeanCloudRuntime.submit config run ⟨entry, input, program.info.resultSchema⟩

/-- Retry one inbox assignment locally. Transport failures never become Cloud
errors. Every attempt checks ownership before touching records; cancellation
returns only after the active attempt and its heartbeat task have stopped. -/
private def executeAssignment (registry : Registry) (config : Config) (id run : String)
    (assignment : Assignment) (finalize : Option Exit := none) : IO Unit := do
  let trace ← Trace.create id run
  repeat
    let revoked ← IO.mkRef false
    try
      Pool.withHeartbeat config run id assignment.attempt fun healthy => do
        let check : IO Unit := do
          healthy
          let allowed : Bool ← IO.ofExcept (fromJson? (← Pool.request config (.check run id assignment.attempt)))
          unless allowed do
            revoked.set true
            throw (IO.userError "Assignment revoked")
        check
        trace.assign assignment
        if finalize.isSome then S3.initializeBucket config.blobs
        let records := trace.records (S3.records config.blobs run)
        let guarded : ReplayStore IO := {
          read := fun key => do check; records.read key
          create := fun key value => do check; records.create key value }
        let observed ← observe guarded
        let report ← match finalize with
          | some outcome => Worker.finalize id observed assignment.attempt outcome
          | none => do
            let definition ← loadRun config run
            let program ← IO.ofExcept (registry.find definition.entry)
            program.execute definition id observed (trace.blobs (S3.storage config.blobs)) trace assignment
        match report.progress with
        | .ok (.fork ..) => trace.emit "suspended" ""
        | .ok .done => trace.emit (if finalize.isSome then "sealed" else "returned") ""
        | .error error => trace.emit "failed" error.message
        Pool.send config (.report run report)
      break
    catch error =>
      if ← revoked.get then
        trace.emit "revoked" ""
        break
      IO.eprintln s!"worker {id}: {error}; retrying assignment locally"
      IO.sleep 500
  trace.emit "idle" ""

/-- One serial inbox loop serves every registered workflow. A cancellation reply
is acknowledged only between attempts. The scheduler awaits that explicit reply
before dispatching replacements. Late execute messages fail their ownership check. -/
def Registry.serveWorker (registry : Registry) (config : Config) : IO Unit := do
  let id ← workerId
  let endpoint ← IO.ofExcept (config.mailboxes.worker id)
  let handle ← HttpMailbox.openMailbox endpoint Pool.address ("worker." ++ id)
  try
    let inbox : Mailbox IO LeanCloud.Pool.Reply := HttpMailbox.inbox handle
    let send := Pool.send config
    let mut nextReady := 0
    IO.println s!"worker {id} ready for deployed programs"
    (← IO.getStdout).flush
    repeat
      if (← IO.monoMsNow) ≥ nextReady then
        send (.ready id)
        nextReady := (← IO.monoMsNow) + 2000
      let some delivery ← inbox.receive | continue
      match delivery.message with
      | .execute run assignment => executeAssignment registry config id run assignment
      | .finalize run attempt outcome =>
        executeAssignment registry config id run ⟨attempt, Location.root⟩ (some outcome)
      | .cancel run barrier => send (.stopped run id barrier)
      | .drain generation => send (.drained id generation)
      | .idle | .acknowledged => pure ()
      match delivery.message with
      | .execute .. | .finalize .. | .cancel .. =>
        -- Readiness and cancellation acknowledgements are confirmed before
        -- dropping the delivery. A process crash can safely redeliver either.
        send (.ready id)
        nextReady := (← IO.monoMsNow) + 2000
      | _ => pure ()
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

def register [Codec ι] [Codec α] (program : CloudProgram ι α)
    (sources : Array ProgramSource := by exact cloud_sources%) :=
  LeanCloudRuntime.registerProgram program sources

/-- Typed submission to the persistent pool. Confirmed registration survives scheduler downtime. -/
def submit [Codec ι] [Codec α] (program : CloudProgram ι α)
    (config : LeanCloudRuntime.Config) (id : String) (input : ι) :=
  LeanCloudRuntime.submitProgram program config id input

end LeanCloud.CloudProgram
