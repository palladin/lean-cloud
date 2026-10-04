import LeanCloud.Core

namespace LeanCloud
open Lean

structure ProgramInfo where
  entry : String
  inputSchema : String
  resultSchema : String
  description : String
  sampleInput : Option Json
  sources : Array ProgramSource := #[]
  deriving FromJson, ToJson, Inhabited

/-- A named compiled entry point. Only its identifier and input cross the wire. -/
structure CloudProgram (ι α : Type) [Codec ι] [Codec α] where
  name : String
  version : String
  description : String := ""
  run : ι → Cloud IO α
  sampleInput : Option ι := none

def CloudProgram.info [Codec ι] [Codec α] (program : CloudProgram ι α) : ProgramInfo := {
  entry := program.name ++ "/" ++ program.version
  inputSchema := (inferInstance : Codec ι).schema
  resultSchema := (inferInstance : Codec α).schema
  description := program.description
  sampleInput := program.sampleInput.map Codec.encode }

end LeanCloud
