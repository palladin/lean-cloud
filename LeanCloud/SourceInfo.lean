import Lean.Data.Json

namespace LeanCloud
open Lean

/-- A source-site identifier is scoped to the deployed application's source map. -/
abbrev SourceSiteId := String

structure SourceSite where
  id : SourceSiteId
  line : Nat
  column : Nat := 0
  endLine : Nat := 0
  endColumn : Nat := 0
  deriving Repr, BEq, FromJson, ToJson, Inhabited

/-- The exact source used to compile this module, bundled with the application. -/
structure ProgramSource where
  file : String
  text : String
  sites : Array SourceSite := #[]
  deriving FromJson, ToJson, Inhabited

end LeanCloud
