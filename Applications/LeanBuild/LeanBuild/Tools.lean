import LeanBuild.Workflow
import LeanBuild.Bundle
import LeanBuild.Workspace
import LeanBuild.Toolchain
import LeanCloudRuntime.Process

namespace LeanBuild
open Lean LeanCloud LeanCloudRuntime

/-- Deployment configuration. Source repositories, Lake targets and build hooks
execute trusted code; the checker sandbox does not sandbox source builds. -/
structure Tools where
  toolchain : System.FilePath
  helper : System.FilePath
  sandbox : Bool := true
  cache : Option Bundle.Cache := none
  threads : Nat := 1

private def withWorkspace (action : System.FilePath → IO α) : IO α :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    action directory

private def project (directory : System.FilePath) (request : Request) : System.FilePath :=
  if request.subdirectory == "." then directory else directory / request.subdirectory

private def run (tools : Tools) (directory : System.FilePath) (limits : Limits)
    (label command : String) (args : Array String)
    (files : Array (System.FilePath × Nat) := #[])
    (cwd : Option System.FilePath := none) (cache : CachePolicy := .rebuild) :
    IO (Except String Unit) := do
  let home := directory / ".." / "home"
  IO.FS.createDirAll home
  let cacheEnv := if cache == .rebuild then #["LAKE_NO_CACHE=true", "LAKE_ARTIFACT_CACHE=false"] else #[]
  let out ← Process.runFiles {
    cmd := "/usr/bin/env", cwd := cwd.getD directory
    args := #["-i", s!"PATH={tools.toolchain / "bin"}:/usr/local/bin:/usr/bin:/bin",
      s!"HOME={home}", s!"LEAN_NUM_THREADS={max 1 tools.threads}",
      "LANG=C.UTF-8", "GIT_TERMINAL_PROMPT=0", "GIT_CONFIG_NOSYSTEM=1"] ++
      cacheEnv ++ #[command] ++ args
  } (limits.seconds * 1000) (directory / ".." / s!"{label}.stdout")
    (directory / ".." / s!"{label}.stderr") (16 * 1024 * 1024) files
  if out.stopped then return .error s!"{label}: time or output limit exceeded"
  if out.exitCode != 0 then
    return .error s!"{label} failed (exit {out.exitCode}): {out.stdout.takeEnd 2000}\n{out.stderr.takeEnd 4000}"
  return .ok ()

private def lake (tools : Tools) (directory : System.FilePath) (request : Request)
    (label : String) (args : Array String)
    (files : Array (System.FilePath × Nat) := #[]) : IO (Except String Unit) :=
  run tools directory request.limits label (tools.toolchain / "bin/lake").toString
    (#[if request.cache == .rebuild then "--no-cache" else "--try-cache", "--keep-toolchain"] ++
      request.options.toArray.map (fun (key, value) => s!"-K{key}={value}") ++ args)
    files (some (project directory request)) request.cache

private def runHelper (tools : Tools) (directory : System.FilePath) (request : Request)
    (label : String) (args : Array String)
    (files : Array (System.FilePath × Nat) := #[]) : IO (Except String Unit) := do
  let library := tools.toolchain / "lib/lean" /
    (if System.Platform.isOSX then "libLake_shared.dylib" else "libLake_shared.so")
  lake tools directory request label (#["env", "lean", s!"-j{max 1 tools.threads}", s!"-M{request.limits.checkerMemoryMiB}",
    "--load-dynlib", library.toString, "--run", tools.helper.toString] ++ args) files

/-- Check the export independently of the project. Never fall back from a
requested sandbox or skip an unavailable checker. -/
def Tools.verifyExport (tools : Tools) (directory : System.FilePath) (limits : Limits)
    (exportPath : System.FilePath) (paranoid : Bool := false) : IO (Except String Unit) :=
  lake tools directory { repository := "", revision := "", limits } "check"
    (#["check", s!"--from-export={exportPath}"] ++
      (if paranoid then #["--paranoid"] else #[]) ++
      (if tools.sandbox then #[] else #["--inadvisably-no-sandbox"]))

private def logs (store : ObjectStore) (directory : System.FilePath) : IO FileRef := do
  let mut texts : Array String := #[]
  for entry in ← (directory / "..").readDir do
    if entry.fileName.endsWith ".stdout" || entry.fileName.endsWith ".stderr" then
      texts := texts.push s!"--- {entry.fileName} ---\n{← IO.FS.readFile entry.path}"
  Files.putText store (String.intercalate "\n" texts.toList)

private def readJson [FromJson α] (path : System.FilePath) : IO α := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)

/-- A minimum supported release, not ABI compatibility between Lean versions. -/
def Tools.sourceRelease (toolchain : String) : Except String String := do
  let invalid := s!"LeanBuild requires a stable leanprover/lean4 release >= 4.35.0; project requires {toolchain}"
  let ["leanprover/lean4", release] := toolchain.splitOn ":v" | throw invalid
  let [major, minor, patch] := release.splitOn "." | throw invalid
  let some major := major.toNat? | throw invalid
  let some minor := minor.toNat? | throw invalid
  let some patch := patch.toNat? | throw invalid
  unless release == s!"{major}.{minor}.{patch}" && (major > 4 || (major == 4 && minor >= 35)) do
    throw invalid
  return release

private def verifyToolchain (tools : Tools) (directory : System.FilePath) : IO String := do
  let expected := (← IO.FS.readFile (directory / "lean-toolchain")).trimAscii.toString
  let release ← IO.ofExcept (Tools.sourceRelease expected)
  let version ← IO.Process.output { cmd := (tools.toolchain / "bin/lean").toString, args := #["--version"] }
  unless version.exitCode == 0 && version.stdout.startsWith s!"Lean (version {release}," do
    throw (IO.userError s!"Project requires {expected}; deploy an image with that exact Lean toolchain")
  return expected

private def platform : IO String := do
  let result ← IO.Process.output { cmd := "uname", args := #["-sm"] }
  unless result.exitCode == 0 do throw (IO.userError "Cannot determine build platform")
  return result.stdout.trimAscii.toString

private def policyFile (directory : System.FilePath) (request : Request) : IO System.FilePath := do
  let path := directory / ".." / "build-request.json"
  IO.FS.writeFile path (toJson request).pretty
  return path

/-- Resolve dependencies and generated inputs once, then freeze their bytes. -/
def Tools.prepareDirectory (tools : Tools) (store : ObjectStore) (request : Request)
    (directory : System.FilePath) (commit : String) : IO Preparation := do
  let prepared : Except String (String × String × Array Module × Bundle.Snapshot) ← try
    let root ← IO.FS.realPath directory
    let cwd ← IO.FS.realPath (project directory request)
    unless cwd == root || cwd.toString.startsWith (root.toString ++ "/") do
      throw (IO.userError "Project directory is outside the repository")
    let toolchain ← verifyToolchain tools cwd
    let policy ← policyFile directory request
    let output := directory / ".." / "build-plan.json"
    IO.ofExcept (← runHelper tools directory request "plan"
      #["plan", policy.toString, output.toString, directory.toString])
    let modules : Array Module ← readJson output
    IO.ofExcept (validateModules modules)
    let source ← Bundle.snapshot directory request.limits.bytes
    pure (.ok (toolchain, ← platform, modules, source))
  catch error => pure (.error (toString error))
  match prepared with
  | .error reason => return { error := reason, diagnostics := ← logs store directory }
  | .ok (toolchain, platform, modules, snapshot) =>
    -- Publication exceptions propagate to Cloud.exec and are durable failures.
    let source ← snapshot.publish store
    return { plan := some { commit, toolchain, platform, modules, source := ← Files.putJson store source } }

def Tools.prepare (tools : Tools) (store : ObjectStore) (request : Request) : IO Preparation :=
  withWorkspace fun directory => do
    let steps := #[
      ("git-init", #["init", "--quiet"]),
      ("git-remote", #["remote", "add", "origin", request.repository]),
      ("git-fetch", #["-c", "protocol.file.allow=never", "fetch", "--depth=1", "origin", request.revision]),
      ("git-checkout", #["checkout", "--detach", "--quiet", "FETCH_HEAD"]),
      ("git-revision", #["rev-parse", "HEAD"])]
    for (label, args) in steps do
      if let .error reason ← run tools directory request.limits label "git" args then
        return { error := reason, diagnostics := ← logs store directory }
    let commit := (← IO.FS.readFile (directory / ".." / "git-revision.stdout")).trimAscii.toString
    if ← (directory / ".gitmodules").pathExists then
      return { error := "Git submodules are not supported; use Lake dependencies" }
    tools.prepareDirectory store request directory commit

/-- Only transitive prerequisites are imported by a parallel module job. -/
private def prerequisites (plan : Plan) (targets : Array Module) : Std.HashSet String := Id.run do
  let mut needed := targets.foldl (fun set m => m.imports.foldl (·.insert ·) set) ({} : Std.HashSet String)
  for m in plan.modules.reverse do
    if needed.contains m.name then
      for dep in m.imports do
        needed := needed.insert dep
  return needed

private def restore (tools : Tools) (store : ObjectStore) (directory : System.FilePath)
    (request : Request) (plan : Plan) (artifacts : Bundle.Manifest)
    (session : Workspace.Session) : IO Bundle.Manifest := do
  unless (← platform) == plan.platform do throw (IO.userError "Build worker platform changed")
  let source ← session.readManifest plan.source
  let workspace := Bundle.overlay source artifacts
  Bundle.synchronize store directory workspace request.limits.bytes tools.cache
  unless (← verifyToolchain tools (project directory request)) == plan.toolchain do
    throw (IO.userError "Toolchain changed since preparation")
  return workspace

private structure ModuleOutcome where
  name : String
  built : Bool
  deriving FromJson

private def buildJob (tools : Tools) (store : ObjectStore) (request : Request)
    (plan : Plan) (completed : Array BuildResult) (modules : Option (Array Module)) : IO (Array BuildResult) := do
  let key := (toJson ("lean-build/workspace/v1", request, plan,
    tools.toolchain.toString, ← Files.digest tools.helper)).compress
  let cache := tools.cache.map fun cache => cache.directory.addExtension "workspace"
  Workspace.use store cache key fun session => do
    let directory := session.directory
    let start ← IO.monoMsNow
    let mut imports : Bundle.Manifest := #[]
    let needed := modules.map (prerequisites plan)
    let mut manifests : Std.HashSet String := {}
    for result in completed do
      if needed.any (fun names => !names.contains result.name) then continue
      let some ref := result.artifacts | throw (IO.userError "Missing prerequisite artifacts")
      if manifests.contains ref.sha256 then continue
      manifests := manifests.insert ref.sha256
      imports ← IO.ofExcept (Bundle.merge imports (← session.readManifest ref))
    let baseline ← restore tools store directory request plan imports session
    let result : Except String (Array BuildResult × Bundle.Snapshot) ← try
      let policy ← policyFile directory request
      let mut results : Array BuildResult := #[]
      if let some group := modules then
        let input := directory / ".." / "module-input.json"
        let output := directory / ".." / "module-results.json"
        IO.FS.writeFile input (toJson (group.map (·.name))).compress
        IO.ofExcept (← runHelper tools directory request "build"
          #["modules", policy.toString, input.toString, output.toString])
        let rows : Array ModuleOutcome ← readJson output
        unless rows.map (·.name) == group.map (·.name) do
          throw (IO.userError "Lake returned incomplete module results")
        let mut failed : Std.HashSet String := {}
        for (m, row) in group.zip rows do
          let blocked := m.imports.any failed.contains
          if !row.built then failed := failed.insert m.name
          results := results.push {
            name := m.name
            status := if row.built then .built else if blocked then .blocked else .failed
            builtModules := if row.built then #[m.name] else #[]
            message := if row.built then "" else if blocked then "A prerequisite failed" else "Lake module build failed; see job diagnostics" }
      else
        let output := directory / ".." / "built-modules.json"
        IO.ofExcept (← runHelper tools directory request "build" #["build", policy.toString, output.toString])
        let names ← readJson output
        results := #[{ name := "targets", status := .built, builtModules := names }]
      let snapshot ← Bundle.delta directory request.limits.bytes baseline
        (if modules.isSome then baseline else #[])
      pure (.ok (results, snapshot))
    catch error => pure (.error (toString error))
    let diagnostics ← logs store directory
    let milliseconds := (← IO.monoMsNow) - start
    match result with
    | .error message => return (modules.map (·.map (·.name)) |>.getD #["targets"]).map fun name =>
        { name, status := .failed, diagnostics, milliseconds, message }
    | .ok (results, snapshot) =>
      -- Failed-only jobs have no artifact consumers. Keep their diagnostics,
      -- without uploading an unreachable pack of partial build outputs.
      if !results.any (·.status == .built) then
        return results.map fun result => { result with diagnostics, milliseconds }
      let changes ← snapshot.publish store
      -- A final workspace manifest includes sources and all outputs, even custom
      -- outputs outside .lake/build. Deletions are respected by taking live paths.
      let artifacts ← if modules.isSome then pure changes else do
        Bundle.existing directory (Bundle.overlay baseline changes)
      let reference ← Files.putJson store artifacts
      if results.all (·.status == .built) then
        session.commit
      return results.map fun result => { result with
        diagnostics, milliseconds, artifacts := if result.status == .built then some reference else none }

def Tools.build (tools : Tools) (store : ObjectStore) (request : Request)
    (plan : Plan) (modules : Array Module) (completed : Array BuildResult) : IO (Array BuildResult) :=
  buildJob tools store request plan completed (some modules)

/-- Lake completes exactly the requested targets: native compilation, linking,
custom targets and any dynamic dependencies remain Lake's responsibility. -/
def Tools.finish (tools : Tools) (store : ObjectStore) (request : Request)
    (plan : Plan) (completed : Array BuildResult) : IO BuildResult := do
  let results ← buildJob tools store request plan completed none
  let some result := results[0]? | throw (IO.userError "Missing target result")
  return result

def Tools.check (tools : Tools) (store : ObjectStore) (request : Request)
    (plan : Plan) (built : BuildResult) : IO CheckResult :=
  withWorkspace fun directory => do
    let start ← IO.monoMsNow
    let some ref := built.artifacts | throw (IO.userError "Missing completed build artifacts")
    -- The final manifest describes the entire completed workspace, including deletions.
    Bundle.restore store directory (← Files.readJson store ref) request.limits.bytes tools.cache
    let exportPath := directory / ".." / "proofs.ndjson"
    let result : Except String (Array Theorem) ← try
      unless (← platform) == plan.platform &&
          (← verifyToolchain tools (project directory request)) == plan.toolchain do
        throw (IO.userError "Checker platform or toolchain changed")
      let policy := directory / ".." / "check-policy.json"
      let modules := directory / ".." / "check-modules.json"
      let output := directory / ".." / "checked-theorems.json"
      IO.FS.writeFile policy (toJson request.check).pretty
      IO.FS.writeFile modules (toJson built.builtModules).pretty
      IO.ofExcept (← runHelper tools directory request "export"
        #["export", policy.toString, modules.toString, exportPath.toString, output.toString]
        #[(exportPath, request.limits.bytes)])
      IO.ofExcept (← tools.verifyExport directory request.limits exportPath (request.check.mode == .paranoid))
      pure (.ok (← readJson output))
    catch error => pure (.error (toString error))
    let diagnostics ← logs store directory
    let milliseconds := (← IO.monoMsNow) - start
    match result with
    | .error message => return { mode := request.check.mode, success := false, diagnostics, milliseconds, message }
    | .ok theorems => return {
        mode := request.check.mode, success := true, diagnostics, milliseconds, theorems
        exportFile := ← Files.upload store exportPath request.limits.bytes }

def Tools.fromEnvironment : IO Tools := do
  let helper := (← IO.getEnv "LEAN_BUILD_HELPER").getD "/opt/lean-build/Helper.lean"
  let toolchain : System.FilePath ← match ← IO.getEnv "LEAN_BUILD_TOOLCHAIN" with
    | some directory => pure (System.FilePath.mk directory)
    | none => do
      match ← IO.getEnv "LEAN_BUILD_RELEASE" with
      | none => pure (System.FilePath.mk "/opt/build-lean")
      | some spec => do
        let cache := (← IO.getEnv "LEAN_BUILD_TOOLCHAINS").getD "/data/toolchains"
        Toolchain.fromFile spec cache helper
  let sandbox ← match (← IO.getEnv "LEAN_BUILD_SANDBOX").getD "1" with
    | "1" => pure true
    | "0" => pure false
    | _ => throw (IO.userError "LEAN_BUILD_SANDBOX must be 0 or 1")
  let cache : Option Bundle.Cache ← match ← IO.getEnv "LEAN_BUILD_CACHE" with
    | none => pure none
    | some directory => do
      let value := (← IO.getEnv "LEAN_BUILD_CACHE_BYTES").getD "4294967296"
      let some bytes := value.toNat? | throw (IO.userError "Invalid LEAN_BUILD_CACHE_BYTES")
      pure (some { directory := directory, bytes : Bundle.Cache })
  return { toolchain := ← IO.FS.realPath toolchain, helper := ← IO.FS.realPath helper, sandbox, cache }

def Tools.backend (tools : Tools) (store : ObjectStore) : Backend IO :=
  let configured := fun env : LeanCloud.Environment => { tools with threads := max 1 env.currentWorker.cpus }
  { prepare := fun env => (configured env).prepare store
    build := fun env => (configured env).build store
    finish := fun env => (configured env).finish store
    check := fun env => (configured env).check store }

end LeanBuild
