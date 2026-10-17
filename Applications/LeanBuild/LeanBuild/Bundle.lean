import LeanBuild.Model

namespace LeanBuild.Bundle
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
  relativePath path

private def skip (path : String) : Bool :=
  path.endsWith ".olean.lock" || path.endsWith "lakefile.olean" ||
  path.endsWith "lakefile.olean.trace" || path.endsWith "lakefile.olean.server" ||
  path.endsWith "lakefile.olean.private"

/-- File links inside the checkout are captured as ordinary files. Never follow
directory links or links outside the workspace. Restored manifests contain no links. -/
private partial def enumerate (root : System.FilePath) (relative : String := "") : IO (Array String) := do
  let mut files := #[]
  for entry in ← (if relative.isEmpty then root else root / relative).readDir do
    let name := if relative.isEmpty then entry.fileName else relative ++ "/" ++ entry.fileName
    let metadata ← entry.path.symlinkMetadata
    match metadata.type with
    | .dir => files := files ++ (← enumerate root name)
    | .file => unless skip name do files := files.push name
    | .symlink =>
      let target ← IO.FS.realPath entry.path
      let rootPrefix := (← IO.FS.realPath root).toString ++ "/"
      unless target.toString.startsWith rootPrefix && (← target.metadata).type == .file do
        throw (IO.userError s!"Symlink must target a file inside the snapshot: {name}")
      unless skip name do files := files.push name
    | _ => throw (IO.userError s!"Unsupported symlink or special file: {name}")
  return files

/-- Locally validated files, ready to publish while the workspace is alive. -/
structure Snapshot where
  root : System.FilePath
  limit : Nat
  paths : Array String

/-- The complete workspace, including generated sources and native outputs. -/
def snapshot (root : System.FilePath) (limit : Nat) : IO Snapshot := do
  let paths ← enumerate root
  let mut total := 0
  for path in paths do
    total := total + (← (root / path).metadata).byteSize.toNat
    unless total ≤ limit do throw (IO.userError "Workspace exceeds configured artifact byte limit")
  return { root, limit, paths }

def existing (root : System.FilePath) (manifest : Manifest) : IO Manifest :=
  manifest.filterM fun entry => do
    let path := root / entry.path
    if !(← path.pathExists) then return false
    return (← path.metadata).type == .file

def Snapshot.publish (snapshot : Snapshot) (store : ObjectStore) : IO Manifest :=
  snapshot.paths.mapM fun (path : String) => do
    return {
      path
      file := ← Files.upload store (snapshot.root / path) snapshot.limit
      executable := ← executable (snapshot.root / path).toString }

/-- Capture changed/new files, including custom outputs outside `.lake/build`.
Parallel module jobs cannot overwrite their immutable prerequisite artifacts.
The final Lake build may legitimately rebuild artifacts when native facets require it. -/
def delta (root : System.FilePath) (limit : Nat) (baseline : Manifest)
    (immutable : Manifest := #[]) : IO Snapshot := do
  let old := baseline.foldl (fun map entry => map.insert entry.path entry) ({} : Std.HashMap String Entry)
  let frozen := immutable.foldl (fun map entry => map.insert entry.path entry) ({} : Std.HashMap String Entry)
  for entry in immutable do
    unless ← (root / entry.path).pathExists do
      throw (IO.userError s!"Build deleted a prerequisite artifact: {entry.path}")
    unless (← (root / entry.path).metadata).type == .file do
      throw (IO.userError s!"Build replaced a prerequisite artifact: {entry.path}")
  let mut paths := #[]
  let mut total := 0
  for path in ← enumerate root do
    let size := (← (root / path).metadata).byteSize.toNat
    total := total + size
    unless total ≤ limit do throw (IO.userError "Workspace exceeds configured artifact byte limit")
    if let some entry := old[path]? then
      if size == entry.file.size && (← Files.digest (root / path)) == entry.file.sha256 &&
          (← executable (root / path).toString) == entry.executable then continue
    if frozen.contains path then
      throw (IO.userError s!"Build changed a prerequisite artifact: {path}")
    paths := paths.push path
  return { root, limit, paths }

/-- Layer build outputs over their source workspace or earlier products.
Concurrent module results use the stricter `merge` operation instead. -/
def overlay (base updates : Manifest) : Manifest :=
  base.filter (fun entry => !updates.any (·.path == entry.path)) ++ updates

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

end LeanBuild.Bundle
