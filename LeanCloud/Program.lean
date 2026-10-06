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
  deriving ToJson, Inhabited

/-- Old deployment/run manifests bundled one file with operation-based sites.
Keep its text, but do not invent precise source identities for those labels. -/
private def legacySources (json : Json) : Except String (Array ProgramSource) := do
  match json.getObjVal? "source" with
  | .error _ | .ok .null => return #[]
  | .ok source =>
    let file ← source.getObjValAs? String "file"
    let text ← source.getObjValAs? String "text"
    return #[{ file, text }]

/-- Source metadata is optional. An explicit modern array remains authoritative,
and malformed non-null arrays are errors rather than discarded metadata. -/
instance : FromJson ProgramInfo where
  fromJson? json := do
    let sources ← match json.getObjVal? "sources" with
      | .error _ | .ok .null => legacySources json
      | .ok sources => fromJson? sources
    return {
      entry := ← json.getObjValAs? String "entry"
      inputSchema := ← json.getObjValAs? String "inputSchema"
      resultSchema := ← json.getObjValAs? String "resultSchema"
      description := ← json.getObjValAs? String "description"
      sampleInput := ← fromJson? ((json.getObjVal? "sampleInput").toOption.getD Json.null)
      sources }

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
