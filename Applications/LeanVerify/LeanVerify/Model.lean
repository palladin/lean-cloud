import LeanCloudRuntime.Files

namespace LeanVerify
open Lean LeanCloud LeanCloudRuntime

/-- Sources and generated artifacts are immutable manifests in the global blob store. -/
abbrev FileRef := LeanCloudRuntime.FileRef

structure Limits where
  seconds : Nat := 600
  checkerMemoryMiB : Nat := 4096
  bytes : Nat := 2 * 1024 * 1024 * 1024
  modules : Nat := 10000
  deriving Repr, ToJson

structure Request where
  repository : String
  revision : String
  modules : Array String
  theorems : Array String := #[]
  allowedAxioms : Array String := #["propext", "Classical.choice", "Quot.sound"]
  limits : Limits := {}
  deriving Repr, ToJson

private def field [FromJson α] (json : Json) (name : String) (fallback : α) : Except String α := do
  match (← json.getObj?)[name]? with
  | none => pure fallback
  | some value => fromJson? value

instance : FromJson Limits where
  fromJson? json := do return {
    seconds := ← field json "seconds" 600
    checkerMemoryMiB := ← field json "checkerMemoryMiB" 4096
    bytes := ← field json "bytes" (2 * 1024 * 1024 * 1024)
    modules := ← field json "modules" 10000 }

instance : FromJson Request where
  fromJson? json := do return {
    repository := ← json.getObjValAs? _ "repository"
    revision := ← json.getObjValAs? _ "revision"
    modules := ← json.getObjValAs? _ "modules"
    theorems := ← field json "theorems" #[]
    allowedAxioms := ← field json "allowedAxioms" #["propext", "Classical.choice", "Quot.sound"]
    limits := ← field json "limits" {} }

private def identifier (s : String) : Bool :=
  !s.isEmpty && (s.splitOn ".").all (fun part => !part.isEmpty &&
    part.toList.all (fun c => c.isAlphanum || c == '_' || c == '\''))

def Request.validate (r : Request) : Except String Unit := do
  let parts := (r.repository.drop "https://github.com/".length).toString.splitOn "/"
  unless r.repository.startsWith "https://github.com/" && parts.length == 2 &&
      parts.all (fun s => !s.isEmpty && s != "." && s != ".." &&
        s.toList.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.')) do
    throw "repository must be a public https://github.com/OWNER/REPOSITORY URL"
  unless !r.revision.isEmpty && r.revision.length ≤ 200 &&
      !r.revision.startsWith "-" && r.revision.toList.all
        (fun c => c.isAlphanum || "-._/".contains c) do
    throw "revision must be a Git commit, branch, or tag"
  unless !r.modules.isEmpty && r.modules.all identifier && r.theorems.all identifier &&
      r.allowedAxioms.all identifier && !r.allowedAxioms.contains "sorryAx" do
    throw "Provide root module names and optional theorem names; sorryAx is never allowed"
  unless 0 < r.limits.seconds && r.limits.seconds ≤ 3600 &&
      64 ≤ r.limits.checkerMemoryMiB && r.limits.checkerMemoryMiB ≤ 65536 &&
      0 < r.limits.bytes && r.limits.bytes ≤ 16 * 1024 * 1024 * 1024 &&
      0 < r.limits.modules && r.limits.modules ≤ 100000 do
    throw "Invalid job limits"

structure Module where
  name : String
  imports : Array String
  deriving Repr, BEq, ToJson, FromJson

structure Plan where
  commit : String
  toolchain : String
  source : FileRef
  modules : Array Module
  deriving Repr, ToJson, FromJson

structure Theorem where
  name : String
  axioms : Array String
  deriving Repr, BEq, ToJson, FromJson

inductive Status where
  | checked | failed | blocked
  deriving Repr, BEq, ToJson, FromJson

structure ModuleResult where
  name : String
  status : Status
  artifacts : Option FileRef := none
  diagnostics : Option FileRef := none
  message : String := ""
  theorems : Array Theorem := #[]
  deriving Repr, ToJson, FromJson

structure Report where
  repository : String
  revision : String
  commit : String := ""
  toolchain : String := ""
  source : Option FileRef := none
  allowedAxioms : Array String := #[]
  success : Bool := false
  message : String := ""
  modules : Array ModuleResult := #[]
  deriving Repr, ToJson, FromJson

structure Preparation where
  plan : Option Plan := none
  diagnostics : Option FileRef := none
  error : String := ""
  deriving Repr, ToJson, FromJson

instance : Codec Request := jsonCodec _ "lean-verify/request/v1"
instance : Codec Preparation := jsonCodec _ "lean-verify/preparation/v1"
instance : Codec ModuleResult := jsonCodec _ "lean-verify/module-result/v1"
instance : Codec Report := jsonCodec _ "lean-verify/report/v1"

/-- Reject malformed, cyclic, duplicate, or incomplete plans before starting jobs. -/
def validateModules (modules : Array Module) : Except String Unit := do
  let mut seen : Array String := #[]
  for m in modules do
    unless identifier m.name && !seen.contains m.name do throw "Duplicate or invalid module"
    unless m.imports.all seen.contains do throw s!"Plan is not topological at {m.name}"
    seen := seen.push m.name

end LeanVerify
