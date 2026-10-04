import LeanCloud.Core

namespace LeanCloud
open Lean

/-- Optional, build-bundled source locations for operations in the terminal view.
An operation with several call sites must not be assigned an ambiguous line. -/
structure SourceSite where
  operation : String
  line : Nat
  deriving FromJson, ToJson, Inhabited

structure ProgramSource where
  file : String
  text : String
  sites : Array SourceSite := #[]
  deriving FromJson, ToJson, Inhabited

structure ProgramInfo where
  entry : String
  inputSchema : String
  resultSchema : String
  description : String
  sampleInput : Option Json
  source : Option ProgramSource
  deriving FromJson, ToJson, Inhabited

/-- A named compiled entry point. Only its identifier and input cross the wire. -/
structure CloudProgram (ι α : Type) [Codec ι] [Codec α] where
  name : String
  version : String
  description : String := ""
  run : ι → Cloud IO α
  sampleInput : Option ι := none
  source : Option ProgramSource := none

def CloudProgram.info [Codec ι] [Codec α] (program : CloudProgram ι α) : ProgramInfo := {
  entry := program.name ++ "/" ++ program.version
  inputSchema := (inferInstance : Codec ι).schema
  resultSchema := (inferInstance : Codec α).schema
  description := program.description
  sampleInput := program.sampleInput.map Codec.encode
  source := program.source }

end LeanCloud
