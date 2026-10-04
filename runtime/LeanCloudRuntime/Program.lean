import LeanCloud.Program
import LeanCloudRuntime.Run

namespace LeanCloudRuntime
open Lean LeanCloud

/-- Existential packaging retains each entry's own input and result codecs. -/
structure RegisteredProgram where
  info : ProgramInfo
  validate : Json → Except String Unit
  worker : Config → String → RunDefinition → IO Unit

def registerProgram [Codec ι] [Codec α] (program : LeanCloud.CloudProgram ι α) : RegisteredProgram where
  info := program.info
  validate input := (Codec.decode (α := ι) input).map (fun _ => ())
  worker config run definition := do
    unless definition.entry == program.info.entry && definition.resultSchema == program.info.resultSchema do
      throw (IO.userError "Worker program version or result codec does not match the submitted run")
    let input ← IO.ofExcept (Codec.decode (α := ι) definition.input)
    runWorker config run program.run input

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

/-- A typed handle can inspect the durable result without a live scheduler. -/
structure CloudProcess (α : Type) [Codec α] where
  config : Config
  id : String
  entry : String

def submitProgram [Codec ι] [Codec α] (program : LeanCloud.CloudProgram ι α)
    (config : Config) (id : String) (input : ι) : IO (CloudProcess α) := do
  Registry.submit ⟨#[registerProgram program]⟩ config id program.info.entry (Codec.encode input)
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

/-- Typed submission to already provisioned services. The console also launches
the scheduler and worker containers; this API only creates the durable run. -/
def submit [Codec ι] [Codec α] (program : CloudProgram ι α)
    (config : LeanCloudRuntime.Config) (id : String) (input : ι) :=
  LeanCloudRuntime.submitProgram program config id input

end LeanCloud.CloudProgram
