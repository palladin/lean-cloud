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

-- The lock protects reservations/eviction, never network transfers.
initialize cacheLock : Std.Mutex Unit ← Std.Mutex.new ()

private structure Pin where
  ref : FileRef
  users : Nat
  ready : Task (Except IO.Error System.FilePath)

-- Access only under cacheLock. Canonical directories also cover path aliases.
private initialize pins : IO.Ref (Std.HashMap String (Std.HashMap String Pin)) ← IO.mkRef {}

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

/-- Validate prepared inputs once after all local compilers have stopped. This
does not scan or republish the build directory after every module. -/
def validateInputs (root : System.FilePath) (inputs : Manifest) (concurrency : Nat) : IO Unit := do
  discard <| Parallel.map concurrency inputs fun entry => do
    if gitIndex entry.path then return
    let path := root / entry.path
    unless (← path.pathExists) && (← path.metadata).type == .file &&
        (← Files.digest path) == entry.file.sha256 && (← executable path.toString) == entry.executable do
      throw (IO.userError s!"Build changed a prerequisite artifact: {entry.path}")

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

/-- One workspace scan yields both the files to upload and the verified entries
to retain. Finalization need not stat every file again after publication. -/
structure Difference where
  changed : Snapshot
  retained : Manifest

/-- Capture changed/new files, including custom outputs outside `.lake/build`.
Parallel module jobs cannot overwrite their immutable prerequisite artifacts.
The final Lake build may legitimately rebuild artifacts when native facets require it. -/
def delta (root : System.FilePath) (limit : Nat) (baseline : Manifest)
    (immutable : Manifest := #[]) (concurrency : Nat := 1) : IO Difference := do
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
    if !immutable.isEmpty && gitIndex path then return (size, none, old[path]?)
    if let some entry := old[path]? then
      if size == entry.file.size && (← Files.digest (root / path)) == entry.file.sha256 &&
          (← executable (root / path).toString) == entry.executable then return (size, none, some entry)
    if frozen.contains path then
      throw (IO.userError s!"Build changed a prerequisite artifact: {path}")
    return (size, some path, none)
  unless checked.foldl (fun total item => total + item.1) 0 ≤ limit do
    throw (IO.userError "Workspace exceeds configured artifact byte limit")
  let paths := checked.filterMap (·.2.1)
  return { changed := { root, limit, paths }, retained := checked.filterMap (·.2.2) }

/-- Publish a potentially large final manifest with bounded concurrent chunks. -/
def publishManifest (store : ObjectStore) (manifest : Manifest) (concurrency : Nat) : IO FileRef := do
  let text := (toJson manifest).compress
  unless text.utf8ByteSize ≤ Files.metadataLimit do throw (IO.userError "Artifact metadata exceeds 256 MiB")
  IO.FS.withTempFile fun handle path => do
    handle.putStr text
    handle.flush
    Files.upload store path Files.metadataLimit concurrency

/-- Layer build outputs over their source workspace or earlier products.
Concurrent module results use the stricter `mergeMany` operation instead. -/
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
    -- A pinned download may rename .pending concurrently; do not stat it.
    if reserved.any (fun ref => entry.fileName == ref.sha256 ||
        entry.fileName == ref.sha256 ++ ".pending") then continue
    let metadata ← entry.path.symlinkMetadata
    unless metadata.type == .file do throw (IO.userError "Invalid pack cache entry")
    if entry.fileName.endsWith ".pending" then
      IO.FS.removeFile entry.path
    else
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
  IO.FS.createDirAll cache.directory
  let key := (← IO.FS.realPath cache.directory).toString
  let held := (← pins.get)[key]?.getD {}
  if held.contains ref.sha256 then return
  let reserved := held.toArray.map (·.2.ref)
  if reserved.foldl (fun n ref => n + ref.size) ref.size > cache.bytes then return
  makeRoom cache (reserved.push ref)
  let pending := cache.directory / (ref.sha256 ++ ".pending")
  try
    let hash ← Digest.copyRange source.toString pending.toString 0 ref.size.toUInt64
    unless hash == ref.sha256 do throw (IO.userError "Published pack changed before caching")
    IO.FS.rename pending (cache.directory / ref.sha256)
  finally
    if ← pending.pathExists then IO.FS.removeFile pending

/-- Choose packing independently of transfer concurrency. Small module artifacts
can share one pack while its chunks upload concurrently. No manifest is returned
until all packs are durable; temporary files outlive every transfer. -/
def Snapshot.publish (snapshot : Snapshot) (store : ObjectStore)
    (cache : Option Cache := none) (concurrency : Nat := 1)
    (packCount : Nat := concurrency) : IO Manifest := do
  if snapshot.paths.isEmpty then return #[]
  let sizes ← Parallel.map concurrency snapshot.paths fun path => do
    return (path, (← (snapshot.root / path).metadata).byteSize.toNat)
  let total := sizes.foldl (fun total item => total + item.2) 0
  unless total ≤ snapshot.limit do throw (IO.userError "Pack exceeds configured byte limit")
  let count := min (max 1 packCount) sizes.size
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

/-- Pin a verified pack until the copy completes. Concurrent readers of the
same pack share one transfer/verification; unrelated packs never wait for it.
If active pins exhaust the cache budget, use private scratch space. -/
private def withPack (store : ObjectStore) (cache : Option Cache) (ref : FileRef)
    (limit concurrency : Nat) (action : System.FilePath → IO Unit) : IO Unit := do
  let privateCopy : IO Unit := IO.FS.withTempDir fun temporary => do
    action (← materialize store temporary ref limit concurrency)
  let some cache := cache | privateCopy
  let lease ← cacheLock.atomically do
    IO.FS.createDirAll cache.directory
    let key := (← IO.FS.realPath cache.directory).toString
    let held := (← pins.get)[key]?.getD {}
    if let some pin := held[ref.sha256]? then
      unless pin.ref.size == ref.size do throw (IO.userError "Conflicting pack size")
      pins.modify (·.insert key (held.insert ref.sha256 { pin with users := pin.users + 1 }))
      return some (key, pin.ready)
    let reserved := held.toArray.map (·.2.ref)
    if reserved.foldl (fun n ref => n + ref.size) ref.size > cache.bytes then
      makeRoom cache reserved
      return none
    makeRoom cache (reserved.push ref)
    let task ← IO.asTask (materialize store cache.directory ref limit concurrency) .dedicated
    pins.modify (·.insert key (held.insert ref.sha256 ⟨ref, 1, task⟩))
    return some (key, task)
  let some (key, task) := lease | privateCopy
  try
    action (← IO.ofExcept (← IO.wait task))
  finally
    cacheLock.atomically do
      let held := (← pins.get)[key]?.getD {}
      if let some pin := held[ref.sha256]? then
        let held := if pin.users ≤ 1 then held.erase ref.sha256
          else held.insert ref.sha256 { pin with users := pin.users - 1 }
        pins.modify fun state => if held.isEmpty then state.erase key else state.insert key held

def restore (store : ObjectStore) (root : System.FilePath) (manifest : Manifest)
    (limit : Nat) (cache : Option Cache := none) (concurrency : Nat := 1) : IO Unit := do
  validate manifest limit
  let groups := manifest.foldl (fun groups entry =>
    groups.insert entry.file.pack.sha256
      ((groups[entry.file.pack.sha256]?).getD #[] |>.push entry))
    ({} : Std.HashMap String (Array Entry))
  let groups := groups.toArray.map (·.2)
  let perPack := max 1 (concurrency / max 1 groups.size)
  discard <| Parallel.map concurrency groups fun entries => do
    let some first := entries[0]? | return
    let ref := first.file.pack
    unless entries.all (·.file.pack == ref) do
      throw (IO.userError "Inconsistent pack references")
    withPack store cache ref limit perPack fun pack =>
      discard <| Parallel.map perPack entries fun entry => do
        let path := root / entry.path
        if let some parent := path.parent then IO.FS.createDirAll parent
        let hash ← Digest.copyRange pack.toString path.toString
          entry.file.offset.toUInt64 entry.file.size.toUInt64 entry.executable
        unless hash == entry.file.sha256 do throw (IO.userError "Packed file digest mismatch")

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
def mergeMany (manifests : Array Manifest) : Except String Manifest := do
  let mut result := #[]
  let mut known : Std.HashMap String Entry := {}
  for manifest in manifests do
    for entry in manifest do
      if let some old := known[entry.path]? then
        unless old.file.sha256 == entry.file.sha256 && old.executable == entry.executable do
          throw s!"Conflicting artifacts: {entry.path}"
      else
        result := result.push entry
        known := known.insert entry.path entry
  return result

end LeanBuild.Bundle
