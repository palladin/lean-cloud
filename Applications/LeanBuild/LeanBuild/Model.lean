import LeanCloudRuntime.Files

namespace LeanBuild
open Lean LeanCloud LeanCloudRuntime

abbrev FileRef := LeanCloudRuntime.FileRef
def standardAxioms : Array String := #["propext", "Classical.choice", "Quot.sound"]

inductive CheckMode where
  | none | kernel | paranoid
  deriving Repr, BEq, ToJson, FromJson

inductive CachePolicy where
  | rebuild | reuse
  deriving Repr, BEq, ToJson, FromJson

structure CheckConfig where
  mode : CheckMode := .none
  theorems : Array String := #[]
  allowedAxioms : Array String := standardAxioms
  deriving Repr, ToJson

structure Limits where
  seconds : Nat := 600
  checkerMemoryMiB : Nat := 4096
  bytes : Nat := 2 * 1024 * 1024 * 1024
  modules : Nat := 10000
  deriving Repr, ToJson

structure Request where
  repository : String
  revision : String
  subdirectory : String := "."
  targets : Array String := #[]
  options : Std.TreeMap String String := {}
  cache : CachePolicy := .rebuild
  check : CheckConfig := {}
  limits : Limits := {}
  deriving Repr, ToJson

private def field [FromJson α] (json : Json) (name : String) (fallback : α) : Except String α := do
  match (← json.getObj?)[name]? with
  | none => pure fallback
  | some value => fromJson? value

instance : FromJson CheckConfig where
  fromJson? json := do return {
    mode := ← field json "mode" .none
    theorems := ← field json "theorems" #[]
    allowedAxioms := ← field json "allowedAxioms" standardAxioms }

instance : FromJson Limits where
  fromJson? json := do return {
    seconds := ← field json "seconds" 600
    checkerMemoryMiB := ← field json "checkerMemoryMiB" 4096
    bytes := ← field json "bytes" (2 * 1024 * 1024 * 1024)
    modules := ← field json "modules" 10000 }

instance : FromJson Request where
  fromJson? json := do
    for old in ["modules", "theorems", "allowedAxioms", "paranoid"] do
      if ((← json.getObj?)[old]?).isSome then
        throw s!"LeanBuild uses targets and an optional check object; remove the old {old} field"
    return {
      repository := ← json.getObjValAs? _ "repository"
      revision := ← json.getObjValAs? _ "revision"
      subdirectory := ← field json "subdirectory" "."
      targets := ← field json "targets" #[]
      options := ← field json "options" {}
      cache := ← field json "cache" .rebuild
      check := ← field json "check" {}
      limits := ← field json "limits" {} }

def identifier (s : String) : Bool :=
  !s.isEmpty && (s.splitOn ".").all (fun part => !part.isEmpty &&
    part.toList.all (fun c => c.isAlphanum || c == '_' || c == '\''))

def relativePath (s : String) : Bool :=
  !s.isEmpty && !s.startsWith "/" && !s.contains '\\' && !s.contains '\x00' &&
    (s.splitOn "/").all (fun p => !p.isEmpty && p != "." && p != "..")

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
  unless r.subdirectory == "." || relativePath r.subdirectory do
    throw "subdirectory must be a relative directory inside the repository"
  -- Lake parses target syntax. Arguments are passed directly, never through a shell.
  unless r.targets.all (fun s => !s.isEmpty && !s.startsWith "-" &&
      !s.startsWith "/" && !(s.splitOn "/").contains ".." &&
      s.toList.all (fun c => c != '\x00' && c != '\n' && c != '\r')) do
    throw "Invalid Lake target"
  unless r.options.toArray.all (fun (key, value) => identifier key && !value.contains '\x00') do
    throw "Invalid Lake configuration option"
  unless r.check.theorems.all identifier do throw "Invalid theorem name"
  unless r.check.allowedAxioms.all standardAxioms.contains do
    throw "Only propext, Classical.choice and Quot.sound may be allowed"
  if r.check.mode == .none && (!r.check.theorems.isEmpty || r.check.allowedAxioms != standardAxioms) then
    throw "Theorem and axiom requirements need check.mode kernel or paranoid"
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
  platform : String
  source : FileRef
  modules : Array Module
  deriving Repr, ToJson, FromJson

inductive Status where
  | built | failed | blocked
  deriving Repr, BEq, ToJson, FromJson

structure BuildResult where
  name : String
  status : Status
  artifacts : Option FileRef := none
  diagnostics : Option FileRef := none
  message : String := ""
  milliseconds : Nat := 0
  builtModules : Array String := #[]
  deriving Repr, ToJson, FromJson

structure Theorem where
  name : String
  axioms : Array String
  deriving Repr, ToJson, FromJson

structure CheckResult where
  mode : CheckMode
  success : Bool
  exportFile : Option FileRef := none
  diagnostics : Option FileRef := none
  theorems : Array Theorem := #[]
  message : String := ""
  milliseconds : Nat := 0
  deriving Repr, ToJson, FromJson

structure Report where
  request : Request
  commit : String := ""
  toolchain : String := ""
  platform : String := ""
  source : Option FileRef := none
  success : Bool := false
  message : String := ""
  modules : Array BuildResult := #[]
  build : BuildResult := { name := "targets", status := .blocked }
  verification : Option CheckResult := none
  deriving Repr, ToJson, FromJson

structure Preparation where
  plan : Option Plan := none
  error : String := ""
  diagnostics : Option FileRef := none
  deriving Repr, ToJson, FromJson

instance : Codec Request := jsonCodec _ "lean-build/request/v1"
instance : Codec Preparation := jsonCodec _ "lean-build/preparation/v1"
instance : Codec BuildResult := jsonCodec _ "lean-build/build-result/v1"
instance : Codec CheckResult := jsonCodec _ "lean-build/check-result/v1"
instance : Codec Report := jsonCodec _ "lean-build/report/v1"

def validateModules (modules : Array Module) : Except String Unit := do
  let mut seen : Array String := #[]
  for m in modules do
    unless identifier m.name && !seen.contains m.name do throw "Duplicate or invalid module"
    unless m.imports.all seen.contains do throw s!"Plan is not topological at {m.name}"
    seen := seen.push m.name

end LeanBuild
