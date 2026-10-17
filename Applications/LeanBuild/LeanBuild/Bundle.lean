import LeanBuild.Model
import Std.Sync.Mutex

namespace LeanBuild.Bundle
open Lean LeanCloudRuntime

/-- Files share a packed blob instead of requiring two remote objects per file. -/
structure PackedFile where
  format : String := "lean-build/packed-file/v1"
  pack : FileRef
  offset : Nat
  size : Nat
  sha256 : String
  deriving Repr, ToJson, FromJson

structure Entry where
  path : String
  file : PackedFile
  executable : Bool := false
  deriving Repr, ToJson, FromJson

abbrev Manifest := Array Entry

structure Cache where
  directory : System.FilePath
  bytes : Nat := 4 * 1024 * 1024 * 1024

-- One worker normally runs one job. Serialize cache access as well for callers
-- that execute jobs concurrently, so eviction never removes a pack being copied.
initialize cacheLock : Std.Mutex Unit ← Std.Mutex.new ()

@[extern "lean_cloud_file_executable"]
opaque executable (path : @& String) : IO Bool

def safePath (path : String) : Bool :=
  relativePath path

private def skip (path : String) : Bool :=
  path.endsWith ".olean.lock" || path.endsWith "lakefile.olean" ||
  path.endsWith "lakefile.olean.trace" || path.endsWith "lakefile.olean.server" ||
  path.endsWith "lakefile.olean.private"

/-- Git refreshes cached file stat data after a checkout is restored elsewhere.
The index is workspace-local bookkeeping, not a parallel build product. HEAD,
tracked source bytes and actual prerequisite artifacts remain protected. -/
private def gitIndex (path : String) : Bool :=
  path == ".git/index" || path.endsWith "/.git/index"

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

def Snapshot.publish (snapshot : Snapshot) (store : ObjectStore) : IO Manifest := do
  if snapshot.paths.isEmpty then return #[]
  IO.FS.withTempFile fun output packPath => do
    let mut entries : Manifest := #[]
    let mut offset := 0
    for path in snapshot.paths do
      let source := snapshot.root / path
      let size := (← source.metadata).byteSize.toNat
      unless offset + size ≤ snapshot.limit do throw (IO.userError "Pack exceeds configured byte limit")
      let hash ← Files.digest source
      let input ← IO.FS.Handle.mk source .read
      let mut remaining := size
      while remaining > 0 do
        let bytes ← input.read (min remaining Files.chunkSize).toUSize
        if bytes.isEmpty then throw (IO.userError "File changed during packing")
        output.write bytes
        remaining := remaining - bytes.size
      unless (← input.read 1).isEmpty && (← Files.digest source) == hash do
        throw (IO.userError "File changed during packing")
      entries := entries.push {
        path, file := { pack := default, offset, size, sha256 := hash }
        executable := ← executable source.toString }
      offset := offset + size
    output.flush
    let pack ← Files.upload store packPath snapshot.limit
    return entries.map fun entry => { entry with file.pack := pack }

/-- Capture changed/new files, including custom outputs outside `.lake/build`.
Parallel module jobs cannot overwrite their immutable prerequisite artifacts.
The final Lake build may legitimately rebuild artifacts when native facets require it. -/
def delta (root : System.FilePath) (limit : Nat) (baseline : Manifest)
    (immutable : Manifest := #[]) : IO Snapshot := do
  let old := baseline.foldl (fun map entry => map.insert entry.path entry) ({} : Std.HashMap String Entry)
  let frozen := immutable.foldl (fun map entry => map.insert entry.path entry) ({} : Std.HashMap String Entry)
  for entry in immutable do
    if gitIndex entry.path then continue
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
    if !immutable.isEmpty && gitIndex path then continue
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
  let paths := updates.foldl (fun paths entry => paths.insert entry.path) ({} : Std.HashSet String)
  base.filter (fun entry => !paths.contains entry.path) ++ updates

/-- Cache only immutable packs; every hit is checked before copying into the
job's private workspace. A corrupt or interrupted cache entry is downloaded again. -/
private def materialize (store : ObjectStore) (cache : System.FilePath)
    (ref : FileRef) (limit : Nat) : IO System.FilePath := do
  IO.ofExcept ref.validate
  unless ref.size ≤ limit do throw (IO.userError "Pack exceeds configured byte limit")
  IO.FS.createDirAll cache
  let path := cache / ref.sha256
  if ← path.pathExists then
    if (← path.metadata).byteSize.toNat == ref.size && (← Files.digest path) == ref.sha256 then
      return path
    IO.FS.removeFile path
  -- A private temporary file prevents a crash from publishing a partial cache entry.
  -- rename is atomic when both paths are on the same filesystem.
  let pending := cache / (ref.sha256 ++ ".pending")
  try
    Files.download store ref pending limit
    IO.FS.rename pending path
  finally
    if ← pending.pathExists then IO.FS.removeFile pending
  return path

private def makeRoom (cache : Cache) (ref : FileRef) : IO Unit := do
  IO.FS.createDirAll cache.directory
  let mut files : Array (System.FilePath × Nat) := #[]
  let mut total := 0
  for entry in ← cache.directory.readDir do
    let metadata ← entry.path.symlinkMetadata
    unless metadata.type == .file do throw (IO.userError "Invalid pack cache entry")
    if entry.fileName.endsWith ".pending" then
      IO.FS.removeFile entry.path
    else if entry.fileName != ref.sha256 then
      let size := metadata.byteSize.toNat
      files := files.push (entry.path, size)
      total := total + size
  for (path, size) in files do
    if total + ref.size ≤ cache.bytes then break
    IO.FS.removeFile path
    total := total - size

def restore (store : ObjectStore) (root : System.FilePath) (manifest : Manifest)
    (limit : Nat) (cache : Option Cache := none) : IO Unit :=
  IO.FS.withTempDir fun temporary => do
    if let some cache := cache then
      cacheLock.atomically do makeRoom cache default
    let mut total := 0
    let mut seen : Std.HashSet String := {}
    let mut groups : Std.HashMap String (Array Entry) := {}
    for entry in manifest do
      IO.ofExcept entry.file.pack.validate
      unless safePath entry.path && !seen.contains entry.path do
        throw (IO.userError "Unsafe or duplicate artifact path")
      seen := seen.insert entry.path
      total := total + entry.file.size
      unless total ≤ limit && entry.file.offset + entry.file.size ≤ entry.file.pack.size &&
          entry.file.pack.size ≤ UInt64.size / 2 && entry.file.format == "lean-build/packed-file/v1" do
        throw (IO.userError "Restored workspace exceeds configured byte limit or pack range")
      groups := groups.insert entry.file.pack.sha256
        ((groups[entry.file.pack.sha256]?).getD #[] |>.push entry)
    for (_, entries) in groups do
      let some first := entries[0]? | continue
      let ref := first.file.pack
      let copy (directory : System.FilePath) : IO Unit := do
        let pack ← materialize store directory ref limit
        for entry in entries do
          unless entry.file.pack == ref do throw (IO.userError "Inconsistent pack references")
          let path := root / entry.path
          if let some parent := path.parent then IO.FS.createDirAll parent
          let hash ← Digest.copyRange pack.toString path.toString
            entry.file.offset.toUInt64 entry.file.size.toUInt64 entry.executable
          unless hash == entry.file.sha256 do throw (IO.userError "Packed file digest mismatch")
      match cache with
      | some cache => cacheLock.atomically do
        if ref.size ≤ cache.bytes then
          -- Reserve the verified size, even when replacing a shorter corrupt file.
          makeRoom cache ref
          copy cache.directory
        else
          copy temporary
          IO.FS.removeFile (temporary / ref.sha256)
      | none =>
        copy temporary
        IO.FS.removeFile (temporary / ref.sha256)

/-- Separate modules may produce the same auxiliary build artifact. Identical
content is shared; differing content is an error, never last-writer-wins. -/
def merge (left right : Manifest) : Except String Manifest := do
  let mut result := left
  let mut known := left.foldl (fun map entry => map.insert entry.path entry) ({} : Std.HashMap String Entry)
  for entry in right do
    if let some old := known[entry.path]? then
      unless old.file.sha256 == entry.file.sha256 && old.executable == entry.executable do
        throw s!"Conflicting artifacts: {entry.path}"
    else
      result := result.push entry
      known := known.insert entry.path entry
  return result

end LeanBuild.Bundle
