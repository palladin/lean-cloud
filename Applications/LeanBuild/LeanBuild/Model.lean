import LeanCloudRuntime.Files

namespace LeanBuild
open Lean LeanCloud LeanCloudRuntime

abbrev FileRef := LeanCloudRuntime.FileRef

inductive CachePolicy where
  | rebuild | reuse
  deriving Repr, BEq, ToJson, FromJson

structure Limits where
  seconds : Nat := 600
  helperMemoryMiB : Nat := 4096
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
  /-- Zero balances CPU use and cloud barriers; nonzero also caps job size. -/
  modulesPerJob : Nat := 0
  limits : Limits := {}
  deriving Repr, ToJson

private def field [FromJson α] (json : Json) (name : String) (fallback : α) : Except String α := do
  match (← json.getObj?)[name]? with
  | none => pure fallback
  | some value => fromJson? value

instance : FromJson Limits where
  fromJson? json := do
    if ((← json.getObj?)["checkerMemoryMiB"]?).isSome then
      throw "Use limits.helperMemoryMiB instead of limits.checkerMemoryMiB"
    return {
      seconds := ← field json "seconds" 600
      helperMemoryMiB := ← field json "helperMemoryMiB" 4096
      bytes := ← field json "bytes" (2 * 1024 * 1024 * 1024)
      modules := ← field json "modules" 10000 }

instance : FromJson Request where
  fromJson? json := do
    for old in ["check", "theorems", "allowedAxioms", "paranoid"] do
      if ((← json.getObj?)[old]?).isSome then
        throw s!"LeanBuild builds Lake targets; independent proof checking was removed. Remove the {old} field"
    if ((← json.getObj?)["modules"]?).isSome then
      throw "Use targets instead of modules"
    return {
      repository := ← json.getObjValAs? _ "repository"
      revision := ← json.getObjValAs? _ "revision"
      subdirectory := ← field json "subdirectory" "."
      targets := ← field json "targets" #[]
      options := ← field json "options" {}
      cache := ← field json "cache" .rebuild
      modulesPerJob := ← field json "modulesPerJob" 0
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
  unless r.modulesPerJob ≤ 100000 do
    throw "modulesPerJob must be 0 (automatic) or between 1 and 100000"
  unless 0 < r.limits.seconds && r.limits.seconds ≤ 3600 &&
      64 ≤ r.limits.helperMemoryMiB && r.limits.helperMemoryMiB ≤ 65536 &&
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
  deriving Repr, ToJson, FromJson

structure Preparation where
  plan : Option Plan := none
  error : String := ""
  diagnostics : Option FileRef := none
  deriving Repr, ToJson, FromJson

instance : Codec Request := jsonCodec _ "lean-build/request/v2"
instance : Codec Preparation := jsonCodec _ "lean-build/preparation/v1"
instance : Codec BuildResult := jsonCodec _ "lean-build/build-result/v1"
instance : Codec Report := jsonCodec _ "lean-build/report/v2"

def validateModules (modules : Array Module) : Except String Unit := do
  let mut seen : Array String := #[]
  for m in modules do
    unless identifier m.name && !seen.contains m.name do throw "Duplicate or invalid module"
    unless m.imports.all seen.contains do throw s!"Plan is not topological at {m.name}"
    seen := seen.push m.name

end LeanBuild
