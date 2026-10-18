import Lean.Data.Json

namespace LeanCloud
open Lean

/-- A source-site identifier is scoped to the deployed application's source map. -/
abbrev SourceSiteId := String

/-- Display metadata for a Cloud helper, bundled with its source sites. -/
structure CloudFunctionInfo where
  name : String
  descr : String
  «opaque» : Bool := true
  deriving Repr, BEq, FromJson, ToJson, Inhabited

structure SourceSite where
  id : SourceSiteId
  line : Nat
  column : Nat := 0
  endLine : Nat := 0
  endColumn : Nat := 0
  functionInfo : Option CloudFunctionInfo := none
  deriving Repr, BEq, ToJson, Inhabited

instance : FromJson SourceSite where
  fromJson? json := do
    return {
      id := ← json.getObjValAs? _ "id"
      line := ← json.getObjValAs? _ "line"
      column := ← json.getObjValAs? _ "column"
      endLine := ← json.getObjValAs? _ "endLine"
      endColumn := ← json.getObjValAs? _ "endColumn"
      -- Existing deployed source maps have no function metadata.
      functionInfo := ← fromJson? ((json.getObjVal? "functionInfo").toOption.getD .null) }

/-- The exact source used to compile this module, bundled with the application. -/
structure ProgramSource where
  file : String
  text : String
  sites : Array SourceSite := #[]
  deriving FromJson, ToJson, Inhabited

end LeanCloud
