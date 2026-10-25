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

private def publishPack (snapshot : Snapshot) (store : ObjectStore) (concurrency : Nat)
    (retain : FileRef → System.FilePath → IO Unit) : IO Manifest := do
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
    let pack ← Files.upload store packPath snapshot.limit concurrency
    retain pack packPath
    return entries.map fun entry => { entry with file.pack := pack }

/-- Capture changed/new files, including custom outputs outside `.lake/build`.
Parallel module jobs cannot overwrite their immutable prerequisite artifacts.
The final Lake build may legitimately rebuild artifacts when native facets require it. -/
def delta (root : System.FilePath) (limit : Nat) (baseline : Manifest)
    (immutable : Manifest := #[]) (concurrency : Nat := 1) : IO Snapshot := do
  let old := baseline.foldl (fun map entry => map.insert entry.path entry) ({} : Std.HashMap String Entry)
  let frozen := immutable.foldl (fun map entry => map.insert entry.path entry) ({} : Std.HashMap String Entry)
  discard <| Parallel.map concurrency immutable fun entry => do
    if gitIndex entry.path then return
    unless ← (root / entry.path).pathExists do
      throw (IO.userError s!"Build deleted a prerequisite artifact: {entry.path}")
    unless (← (root / entry.path).metadata).type == .file do
      throw (IO.userError s!"Build replaced a prerequisite artifact: {entry.path}")
  let checked ← Parallel.map concurrency (← enumerate root) fun path => do
    let size := (← (root / path).metadata).byteSize.toNat
    if !immutable.isEmpty && gitIndex path then return (size, none)
    if let some entry := old[path]? then
      if size == entry.file.size && (← Files.digest (root / path)) == entry.file.sha256 &&
          (← executable (root / path).toString) == entry.executable then return (size, none)
    if frozen.contains path then
      throw (IO.userError s!"Build changed a prerequisite artifact: {path}")
    return (size, some path)
  unless checked.foldl (fun total item => total + item.1) 0 ≤ limit do
    throw (IO.userError "Workspace exceeds configured artifact byte limit")
  let paths := checked.filterMap (·.2)
  return { root, limit, paths }

/-- Layer build outputs over their source workspace or earlier products.
Concurrent module results use the stricter `merge` operation instead. -/
def overlay (base updates : Manifest) : Manifest :=
  let paths := updates.foldl (fun paths entry => paths.insert entry.path) ({} : Std.HashSet String)
  base.filter (fun entry => !paths.contains entry.path) ++ updates

/-- Cache only immutable packs; every hit is checked before copying into the
job's private workspace. A corrupt or interrupted cache entry is downloaded again. -/
private def materialize (store : ObjectStore) (cache : System.FilePath)
    (ref : FileRef) (limit concurrency : Nat) : IO System.FilePath := do
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
    Files.download store ref pending limit concurrency
    IO.FS.rename pending path
  finally
    if ← pending.pathExists then IO.FS.removeFile pending
  return path

private def makeRoom (cache : Cache) (reserved : Array FileRef) : IO Unit := do
  IO.FS.createDirAll cache.directory
  let mut files : Array (System.FilePath × Nat) := #[]
  let mut total := 0
  for entry in ← cache.directory.readDir do
    let metadata ← entry.path.symlinkMetadata
    unless metadata.type == .file do throw (IO.userError "Invalid pack cache entry")
    if entry.fileName.endsWith ".pending" then
      IO.FS.removeFile entry.path
    else if !reserved.any (fun ref => ref.sha256 == entry.fileName) then
      let size := metadata.byteSize.toNat
      files := files.push (entry.path, size)
      total := total + size
  let reservedBytes := reserved.foldl (fun total ref => total + ref.size) 0
  for (path, size) in files do
    if total + reservedBytes ≤ cache.bytes then break
    IO.FS.removeFile path
    total := total - size

/-- Keep a producer's verified pack locally too: later assignments need not
download bytes this worker just uploaded. Called under the cache lock. -/
private def retainPack (cache : Cache) (ref : FileRef) (source : System.FilePath) : IO Unit := do
  if ref.size > cache.bytes then return
  makeRoom cache #[ref]
  let pending := cache.directory / (ref.sha256 ++ ".pending")
  try
    let hash ← Digest.copyRange source.toString pending.toString 0 ref.size.toUInt64
    unless hash == ref.sha256 do throw (IO.userError "Published pack changed before caching")
    IO.FS.rename pending (cache.directory / ref.sha256)
  finally
    if ← pending.pathExists then IO.FS.removeFile pending

/-- Pack, hash and upload independent groups within one CPU/IO budget. Large
single files instead use parallel chunk transfers. No manifest is returned until
all packs are durable; temporary files remain alive until every task stops. -/
def Snapshot.publish (snapshot : Snapshot) (store : ObjectStore)
    (cache : Option Cache := none) (concurrency : Nat := 1) : IO Manifest := do
  if snapshot.paths.isEmpty then return #[]
  let sizes ← Parallel.map concurrency snapshot.paths fun path => do
    return (path, (← (snapshot.root / path).metadata).byteSize.toNat)
  let total := sizes.foldl (fun total item => total + item.2) 0
  unless total ≤ snapshot.limit do throw (IO.userError "Pack exceeds configured byte limit")
  let count := min (max 1 concurrency) sizes.size
  -- Assign large files first to the currently smallest pack. This only groups
  -- immutable file bytes; it does not change build dependencies or scheduling.
  let groups := (sizes.qsort (fun a b => a.2 > b.2)).foldl (fun groups item =>
    let target := (Array.range count).foldl
      (fun best i => if groups[i]!.1 < groups[best]!.1 then i else best) 0
    groups.modify target fun (size, paths) => (size + item.2, paths.push item.1))
    (Array.replicate count (0, (#[] : Array String)))
  let groups := groups.filter (!·.2.isEmpty)
  let retain := fun ref path => match cache with
    | none => pure ()
    | some cache => cacheLock.atomically do retainPack cache ref path
  let manifests ← Parallel.map concurrency groups fun (limit, paths) =>
    publishPack { snapshot with paths, limit } store
      (if groups.size == 1 then concurrency else 1) retain
  return manifests.flatten

private def validate (manifest : Manifest) (limit : Nat) : IO Unit := do
  let mut total := 0
  let mut seen : Std.HashSet String := {}
  for entry in manifest do
    IO.ofExcept entry.file.pack.validate
    unless safePath entry.path && !seen.contains entry.path do
      throw (IO.userError "Unsafe or duplicate artifact path")
    seen := seen.insert entry.path
    total := total + entry.file.size
    unless total ≤ limit && entry.file.offset + entry.file.size ≤ entry.file.pack.size &&
        entry.file.pack.size ≤ UInt64.size / 2 && entry.file.format == "lean-build/packed-file/v1" do
      throw (IO.userError "Restored workspace exceeds configured byte limit or pack range")
  for entry in manifest do
    let mut ancestor := ""
    for component in (entry.path.splitOn "/").dropLast do
      ancestor := if ancestor.isEmpty then component else ancestor ++ "/" ++ component
      if seen.contains ancestor then throw (IO.userError "Artifact file is also a directory")

def restore (store : ObjectStore) (root : System.FilePath) (manifest : Manifest)
    (limit : Nat) (cache : Option Cache := none) (concurrency : Nat := 1) : IO Unit := do
  validate manifest limit
  IO.FS.withTempDir fun temporary => do
    let groups := manifest.foldl (fun groups entry =>
      groups.insert entry.file.pack.sha256
        ((groups[entry.file.pack.sha256]?).getD #[] |>.push entry))
      ({} : Std.HashMap String (Array Entry))
    let groups := groups.toArray.map (·.2)
    let restoreAll : IO Unit := do
      if let some cache := cache then makeRoom cache #[]
      let width := max 1 concurrency
      let mut index := 0
      while index < groups.size do
        let batch := groups.extract index (index + width)
        -- Pin this batch before starting its tasks. Entries that do not fit use
        -- private scratch files. No eviction or .pending cleanup runs mid-batch.
        let mut reserved : Array FileRef := #[]
        let mut bytes := 0
        if let some cache := cache then
          for entries in batch do
            if let some entry := entries[0]? then
              let ref := entry.file.pack
              if bytes + ref.size ≤ cache.bytes then
                reserved := reserved.push ref
                bytes := bytes + ref.size
          makeRoom cache reserved
        let perPack := max 1 (width / batch.size)
        discard <| Parallel.map width batch fun entries => do
          let some first := entries[0]? | return
          let ref := first.file.pack
          unless entries.all (·.file.pack == ref) do
            throw (IO.userError "Inconsistent pack references")
          let cached := reserved.contains ref
          let directory := match cache with
            | some cache => if cached then cache.directory else temporary
            | none => temporary
          let pack ← materialize store directory ref limit perPack
          discard <| Parallel.map perPack entries fun entry => do
            let path := root / entry.path
            if let some parent := path.parent then IO.FS.createDirAll parent
            let hash ← Digest.copyRange pack.toString path.toString
              entry.file.offset.toUInt64 entry.file.size.toUInt64 entry.executable
            unless hash == entry.file.sha256 do throw (IO.userError "Packed file digest mismatch")
          unless cached do IO.FS.removeFile pack
        index := index + width
    -- Serialize cache users, while each user processes its pinned packs/files
    -- concurrently. The caller's workspace is private and never shared.
    match cache with
    | some _ => cacheLock.atomically do restoreAll
    | none => restoreAll

/-- Reconcile a clean cached workspace with exactly this job's committed inputs.
Keep verified files in place; fetch only missing/changed files. Outputs not in
these inputs are removed, so a replay cannot accidentally reuse its own results. -/
def synchronize (store : ObjectStore) (root : System.FilePath) (desired : Manifest)
    (limit : Nat) (cache : Option Cache := none) (concurrency : Nat := 1) : IO Unit := do
  validate desired limit
  let paths := desired.foldl (fun set entry => set.insert entry.path) ({} : Std.HashSet String)
  for path in ← enumerate root do
    if !paths.contains path then IO.FS.removeFile (root / path)
  let checked ← Parallel.map concurrency desired fun entry => do
    let path := root / entry.path
    if ← path.pathExists then
      unless (← path.symlinkMetadata).type == .file do
        throw (IO.userError s!"Invalid cached workspace file: {entry.path}")
      if (← path.metadata).byteSize.toNat == entry.file.size &&
          (← Files.digest path) == entry.file.sha256 &&
          (← executable path.toString) == entry.executable then return none
    return some entry
  restore store root (checked.filterMap id) limit cache concurrency

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
