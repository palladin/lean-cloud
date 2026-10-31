import LeanBuild.Bundle

namespace LeanBuild.Workspace
open Lean LeanCloudRuntime

private structure Saved where
  key : String
  manifests : Array (FileRef × Bundle.Manifest)
  deriving ToJson, FromJson

private structure Cached where
  ref : FileRef
  manifest : Bundle.Manifest
  validated : Bool := false

/-- A worker-local cache, never a source of durable build progress. -/
structure Session where
  directory : System.FilePath
  readManifest : FileRef → IO Bundle.Manifest
  rememberManifest : FileRef → Bundle.Manifest → IO Unit
  commit : IO Unit

-- Each process owns its cache directory. Also serialize callers in that process.
initialize lock : Std.Mutex Unit ← Std.Mutex.new ()

private def session (store : ObjectStore) (root : System.FilePath) (key : String)
    (saved : Option Saved) (persistent : Bool) (concurrency : Nat) (action : Session → IO α) : IO α := do
  IO.FS.createDirAll (root / "project")
  let entries := saved.map (·.manifests) |>.getD #[]
  let manifests ← Std.Mutex.new (entries.foldl (fun map (ref, manifest) =>
    map.insert ref.sha256 { ref, manifest : Cached }) ({} : Std.HashMap String Cached))
  let remember := fun ref manifest => manifests.atomically do
    modify (·.insert ref.sha256 { ref, manifest, validated := true })
  action {
    directory := root / "project"
    readManifest := fun ref => do
      if let some entry := (← manifests.atomically get)[ref.sha256]? then
        let manifest := entry.manifest
        if entry.ref == ref && entry.validated then return manifest
        -- Manifests are published by Files.putJson. Treat cached metadata like
        -- cached files: corruption must never change the committed inputs.
        let json := toJson manifest
        let validEncoding (text : String) : IO Bool := do
          let bytes := text.toUTF8
          return bytes.size == ref.size && (← Digest.bytes bytes) == ref.sha256
        if ← validEncoding json.compress then
          remember ref manifest
          return manifest
      let manifest ← Files.readJson store ref concurrency
      remember ref manifest
      return manifest
    rememberManifest := remember
    commit := do
      if persistent then
        let value : Saved := { key, manifests := (← manifests.atomically get).toArray.map fun (_, e) => (e.ref, e.manifest) }
        IO.FS.writeFile (root / "ready.pending") (toJson value).compress
        IO.FS.rename (root / "ready.pending") (root / "ready.json") }

/-- Keep one prepared workspace per worker, bounded by the request's workspace
limit. A different build replaces it. Remove the clean marker before any work:
a crash, exception, or unsuccessful job leaves no reusable checkpoint. The next
attempt discards it and restores committed blob artifacts. -/
def use (store : ObjectStore) (cache : Option System.FilePath) (key : String)
    (action : Session → IO α) (concurrency : Nat := 1) : IO α :=
  match cache with
  | none => IO.FS.withTempDir fun root => session store root key none false concurrency action
  | some root => lock.atomically do
    let saved : Option Saved ← try
      let value ← IO.ofExcept (Json.parse (← IO.FS.readFile (root / "ready.json")) >>= fromJson?)
      pure (if value.key == key then some value else none)
    catch _ => pure none
    if saved.isNone && (← root.pathExists) then IO.FS.removeDirAll root
    IO.FS.createDirAll root
    -- Clear previous logs, helper result files and the clean marker. Keep only
    -- the source/build tree; stale result files must never hide a helper error.
    for entry in ← root.readDir do
      if entry.fileName != "project" then
        if (← entry.path.symlinkMetadata).type == .dir then IO.FS.removeDirAll entry.path
        else IO.FS.removeFile entry.path
    session store root key saved true concurrency action

end LeanBuild.Workspace
