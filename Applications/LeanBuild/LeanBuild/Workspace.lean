import LeanBuild.Bundle

namespace LeanBuild.Workspace
open Lean LeanCloudRuntime

private structure Saved where
  key : String
  manifests : Array (FileRef × Bundle.Manifest)
  deriving ToJson, FromJson

/-- A worker-local cache, never a source of durable build progress. -/
structure Session where
  directory : System.FilePath
  readManifest : FileRef → IO Bundle.Manifest
  rememberManifest : FileRef → Bundle.Manifest → IO Unit
  commit : IO Unit

-- Each process owns its cache directory. Also serialize callers in that process.
initialize lock : Std.Mutex Unit ← Std.Mutex.new ()

private def session (store : ObjectStore) (root : System.FilePath) (key : String)
    (saved : Option Saved) (persistent : Bool) (action : Session → IO α) : IO α := do
  IO.FS.createDirAll (root / "project")
  let manifests ← Std.Mutex.new (saved.map (·.manifests) |>.getD #[])
  let remember := fun ref manifest => manifests.atomically do
    modify fun entries => (entries.filter (·.1 != ref)).push (ref, manifest)
  action {
    directory := root / "project"
    readManifest := fun ref => do
      if let some (_, manifest) := (← manifests.atomically get).find? (fun entry => entry.1 == ref) then
        -- Manifests are published by Files.putJson. Treat cached metadata like
        -- cached files: corruption must never change the committed inputs.
        let bytes := (toJson manifest).pretty.toUTF8
        if bytes.size == ref.size && (← Digest.bytes bytes) == ref.sha256 then
          return manifest
      let manifest ← Files.readJson store ref
      remember ref manifest
      return manifest
    rememberManifest := remember
    commit := do
      if persistent then
        let value : Saved := { key, manifests := ← manifests.atomically get }
        IO.FS.writeFile (root / "ready.pending") (toJson value).compress
        IO.FS.rename (root / "ready.pending") (root / "ready.json") }

/-- Keep one prepared workspace per worker, bounded by the request's workspace
limit. A different build replaces it. Remove the clean marker before any work:
a crash, exception, or unsuccessful job leaves no reusable checkpoint. The next
attempt discards it and restores committed blob artifacts. -/
def use (store : ObjectStore) (cache : Option System.FilePath) (key : String)
    (action : Session → IO α) : IO α :=
  match cache with
  | none => IO.FS.withTempDir fun root => session store root key none false action
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
    session store root key saved true action

end LeanBuild.Workspace
