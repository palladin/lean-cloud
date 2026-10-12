import LeanVerify.Model

namespace LeanVerify.Bundle
open Lean LeanCloudRuntime

structure Entry where
  path : String
  file : FileRef
  executable : Bool := false
  deriving Repr, ToJson, FromJson

abbrev Manifest := Array Entry

@[extern "lean_cloud_file_executable"]
opaque executable (path : @& String) : IO Bool

def safePath (path : String) : Bool :=
  !path.isEmpty && !path.startsWith "/" && !path.contains '\\' && !path.contains '\x00' &&
  (path.splitOn "/").all (fun p => !p.isEmpty && p != "." && p != "..")

def isBuild (path : String) : Bool := (path.splitOn "/.lake/build/").length > 1 ||
  path.startsWith ".lake/build/"

private def skip (path : String) : Bool :=
  path.endsWith ".olean.lock" || path.endsWith "lakefile.olean" ||
  path.endsWith "lakefile.olean.trace" || path.endsWith "lakefile.olean.server" ||
  path.endsWith "lakefile.olean.private"

/-- Do not follow links into the worker's filesystem. Each manifest is size bounded
and each destination is relative to a new, exclusively owned workspace. -/
private partial def enumerate (root : System.FilePath) (relative : String := "") : IO (Array String) := do
  let mut files := #[]
  for entry in ← (if relative.isEmpty then root else root / relative).readDir do
    let name := if relative.isEmpty then entry.fileName else relative ++ "/" ++ entry.fileName
    let metadata ← entry.path.symlinkMetadata
    match metadata.type with
    | .dir => files := files ++ (← enumerate root name)
    | .file => unless skip name do files := files.push name
    | _ => throw (IO.userError s!"Unsupported symlink or special file: {name}")
  return files

def capture (store : ObjectStore) (root : System.FilePath) (limit : Nat)
    (build : Bool) (previous : Manifest := #[]) : IO Manifest := do
  let mut total := 0
  let mut entries := #[]
  for path in ← enumerate root do
    if isBuild path != build then continue
    let size := (← (root / path).metadata).byteSize.toNat
    total := total + size
    unless total ≤ limit do throw (IO.userError "Workspace exceeds configured artifact byte limit")
    let hash ← Files.digest (root / path)
    if let some old := previous.find? (·.path == path) then
      unless hash == old.file.sha256 do
        throw (IO.userError s!"Build changed a prerequisite artifact: {path}")
    else
      entries := entries.push {
        path
        file := ← Files.upload store (root / path) limit
        executable := ← executable (root / path).toString }
  return entries

def restore (store : ObjectStore) (root : System.FilePath) (manifest : Manifest)
    (limit : Nat) : IO Unit := do
  let mut total := 0
  let mut seen : Array String := #[]
  for entry in manifest do
    unless safePath entry.path && !seen.contains entry.path do
      throw (IO.userError "Unsafe or duplicate artifact path")
    seen := seen.push entry.path
    total := total + entry.file.size
    unless total ≤ limit do throw (IO.userError "Restored workspace exceeds configured byte limit")
    let path := root / entry.path
    if let some parent := path.parent then IO.FS.createDirAll parent
    Files.download store entry.file path limit
    if entry.executable then
      let out ← IO.Process.output { cmd := "chmod", args := #["u+x", path.toString] }
      unless out.exitCode == 0 do throw (IO.userError "Cannot restore executable permission")

/-- Separate modules may produce the same auxiliary build artifact. Identical
content is shared; differing content is an error, never last-writer-wins. -/
def merge (left right : Manifest) : Except String Manifest := do
  let mut result := left
  for entry in right do
    if let some old := result.find? (·.path == entry.path) then
      unless old.file.sha256 == entry.file.sha256 && old.executable == entry.executable do
        throw s!"Conflicting artifacts: {entry.path}"
    else result := result.push entry
  return result

end LeanVerify.Bundle
