import LeanBuild.Workflow
import LeanBuild.Bundle
import LeanBuild.Workspace
import LeanBuild.Toolchain
import LeanBuild.Builders
import LeanCloudRuntime.Process

namespace LeanBuild
open Lean LeanCloud LeanCloudRuntime

/-- Deployment configuration. Source repositories, Lake targets and build hooks
execute trusted code inside the worker container. -/
structure Tools where
  toolchain : System.FilePath
  helper : System.FilePath
  cache : Option Bundle.Cache := none
  threads : Nat := 1
  cancelled : IO Bool := pure false

private def withWorkspace (action : System.FilePath → IO α) : IO α :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    action directory

private def project (directory : System.FilePath) (request : Request) : System.FilePath :=
  if request.subdirectory == "." then directory else directory / request.subdirectory

private def run (tools : Tools) (directory : System.FilePath) (limits : Limits)
    (label command : String) (args : Array String)
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
    (directory / ".." / s!"{label}.stderr") (16 * 1024 * 1024) (cancelled := tools.cancelled)
  if out.stopped then return .error s!"{label}: time or output limit exceeded"
  if out.exitCode != 0 then
    return .error s!"{label} failed (exit {out.exitCode}): {out.stdout.takeEnd 2000}\n{out.stderr.takeEnd 4000}"
  return .ok ()

private def lake (tools : Tools) (directory : System.FilePath) (request : Request)
    (label : String) (args : Array String) : IO (Except String Unit) :=
  run tools directory request.limits label (tools.toolchain / "bin/lake").toString
    (#[if request.cache == .rebuild then "--no-cache" else "--try-cache", "--keep-toolchain"] ++
      request.options.toArray.map (fun (key, value) => s!"-K{key}={value}") ++ args)
    (some (project directory request)) request.cache

private def runHelper (tools : Tools) (directory : System.FilePath) (request : Request)
    (label : String) (args : Array String) : IO (Except String Unit) := do
  let library := tools.toolchain / "lib/lean" /
    (if System.Platform.isOSX then "libLake_shared.dylib" else "libLake_shared.so")
  lake tools directory request label (#["env", "lean", s!"-j{max 1 tools.threads}", s!"-M{request.limits.helperMemoryMiB}",
    "--load-dynlib", library.toString, "--run", tools.helper.toString] ++ args)

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
    let source ← snapshot.publish store tools.cache tools.threads
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
      let args := #["-c", s!"pack.threads={max 1 tools.threads}",
        "-c", s!"index.threads={max 1 tools.threads}"] ++ args
      if let .error reason ← run tools directory request.limits label "git" args then
        return { error := reason, diagnostics := ← logs store directory }
    let commit := (← IO.FS.readFile (directory / ".." / "git-revision.stdout")).trimAscii.toString
    if ← (directory / ".gitmodules").pathExists then
      return { error := "Git submodules are not supported; use Lake dependencies" }
    tools.prepareDirectory store request directory commit

private def restore (tools : Tools) (store : ObjectStore) (directory : System.FilePath)
    (request : Request) (plan : Plan) (artifacts : Bundle.Manifest)
    (session : Workspace.Session) : IO Bundle.Manifest := do
  unless (← platform) == plan.platform do throw (IO.userError "Build worker platform changed")
  let source ← session.readManifest plan.source
  let workspace := Bundle.overlay source artifacts
  Bundle.synchronize store directory workspace request.limits.bytes tools.cache tools.threads
  unless (← verifyToolchain tools (project directory request)) == plan.toolchain do
    throw (IO.userError "Toolchain changed since preparation")
  return workspace

private def workspaceKey (tools : Tools) (request : Request) (plan : Plan) : IO String := do
  return (toJson ("lean-build/workspace/v1", request, plan,
    tools.toolchain.toString, ← Files.digest tools.helper)).compress

/-- Final Lake targets can include native compilation, linking and custom outputs. -/
private def finishTargets (tools : Tools) (store : ObjectStore) (request : Request)
    (plan : Plan) (completed : Array BuildResult) (progress : ProgressReporter IO) : IO BuildResult := do
  let key ← workspaceKey tools request plan
  let cache := tools.cache.map fun cache => cache.directory.addExtension "workspace"
  Workspace.use store cache key fun session => do
    let directory := session.directory
    let start ← IO.monoMsNow
    progress.report "finalize" { message := "Collecting artifact manifests" }
    let references ← completed.mapM fun result => do
      let some ref := result.artifacts | throw (IO.userError "Missing prerequisite artifacts")
      return ref
    let downloaded ← Parallel.map tools.threads references session.readManifest
    let imports ← IO.ofExcept (Bundle.mergeMany downloaded)
    progress.report "finalize" { message := "Restoring and verifying cached artifacts" }
    let baseline ← restore tools store directory request plan imports session
    let result : Except String (Array String × Bundle.Difference) ← try
      progress.report "finalize" { message := "Completing Lake targets" }
      let policy ← policyFile directory request
      let output := directory / ".." / "built-modules.json"
      IO.ofExcept (← runHelper tools directory request "build" #["build", policy.toString, output.toString])
      let names ← readJson output
      progress.report "finalize" { message := "Verifying final workspace" }
      pure (.ok (names, ← Bundle.delta directory request.limits.bytes baseline #[] tools.threads))
    catch error => pure (.error (toString error))
    let diagnostics ← logs store directory
    let milliseconds := (← IO.monoMsNow) - start
    match result with
    | .error message => return { name := "targets", status := .failed, diagnostics, milliseconds, message }
    | .ok (builtModules, difference) =>
      progress.report "finalize" { message := "Publishing final workspace" }
      let changes ← difference.changed.publish store tools.cache tools.threads
      let artifacts := difference.retained ++ changes
      let reference ← Bundle.publishManifest store artifacts tools.threads
      session.rememberManifest reference artifacts
      session.commit
      progress.report "finalize" { message := "Finished" }
      return { name := "targets", status := .built, diagnostics, milliseconds := (← IO.monoMsNow) - start, artifacts := some reference, builtModules }

private structure Installed where
  modules : Std.HashMap String FileRef := {}
  files : Std.HashMap String Bundle.Entry := {}

private def Installed.remember (state : Installed) (entries : Bundle.Manifest) : Except String Installed := do
  let mut files := state.files
  for entry in entries do
    if let some old := files[entry.path]? then
      unless old.file.sha256 == entry.file.sha256 && old.executable == entry.executable do
        throw s!"Conflicting artifacts: {entry.path}"
    else files := files.insert entry.path entry
  return { state with files }

private structure ModuleCompletion where
  name : String
  success : Bool
  paths : Array String
  diagnostics : String
  deriving FromJson

/-- Drain atomic completion files without waiting for the first/slowest module.
Lake compiles while a bounded IO pool packs and uploads completed artifacts.
On any publication error, stop and join Lake before releasing the workspace. -/
private def buildBatch (tools : Tools) (store : ObjectStore) (env : Environment IO)
    (directory : System.FilePath) (request : Request) (policy : System.FilePath)
    (session : Workspace.Session) (installed : Std.Mutex Installed)
    (cancellation : CancellationToken IO) (modules : Array Module)
    (publish : BuildResult → IO Unit) : IO Unit := do
  let output := directory / ".." / "module-results"
  if ← output.pathExists then IO.FS.removeDirAll output
  IO.FS.createDir output
  let input := directory / ".." / "module-batch.json"
  IO.FS.writeFile input (toJson (modules.map (·.name))).compress
  let abort ← IO.mkRef false
  let localTools := { tools with cancelled := do return (← abort.get) || (← cancellation.isRequested) }
  let start ← IO.monoMsNow
  env.progress.report "lake" { message := s!"Building {modules.size} modules · {tools.threads} CPUs", total := some modules.size }
  let task ← IO.asTask (runHelper localTools directory request "modules"
    #["modules", policy.toString, input.toString, output.toString, directory.toString]) .dedicated
  try
    let pending ← Std.Mutex.new (Array.range modules.size)
    let completed ← Std.Mutex.new (0 : Nat)
    let failures ← IO.mkRef false
    -- Publishers claim whichever completion is ready. One slow upload must not
    -- prevent another slot from noticing and publishing later completions.
    discard <| Parallel.map tools.threads (Array.range (max 1 tools.threads)) fun _ => do
      try
        repeat
          if ← localTools.cancelled then break
          let (index?, done) ← pending.atomically do
            let indices ← get
            -- Check process completion before scanning its atomic reports.
            let finished ← IO.hasFinished task
            for position in [:indices.size] do
              let index := indices[position]!
              if ← (output / s!"{index}.json").pathExists then
                set (indices.eraseIdxIfInBounds position)
                return (some index, false)
            return (none, finished || indices.isEmpty)
          let some index := index? | do
            if done then break
            IO.sleep 20
            continue
          let some m := modules[index]? | throw (IO.userError "Invalid module result index")
          let value : ModuleCompletion ← readJson (output / s!"{index}.json")
          unless value.name == m.name do throw (IO.userError "Module completion name mismatch")
          if ← localTools.cancelled then break
          let diagnostics ← Files.putText store s!"{m.name}\n{value.diagnostics}"
          if !value.success then
            failures.set true
            publish { name := m.name, status := .failed, diagnostics, milliseconds := (← IO.monoMsNow) - start, message := "Lake module compilation failed" }
          else
            unless !value.paths.isEmpty && value.paths.all Bundle.safePath do
              throw (IO.userError "Invalid module artifact paths")
            let snapshot : Bundle.Snapshot := { root := directory, limit := request.limits.bytes, paths := value.paths }
            -- Parallelize across completed modules, not nested full-sized pools.
            let manifest ← snapshot.publish store tools.cache 1
            let artifacts ← Files.putJson store manifest
            installed.atomically do
              let state ← IO.ofExcept ((← get).remember manifest)
              set { state with modules := state.modules.insert m.name artifacts }
            session.rememberManifest artifacts manifest
            publish { name := m.name, status := .built, artifacts, diagnostics, milliseconds := (← IO.monoMsNow) - start, builtModules := #[m.name] }
          completed.atomically do
            modify (· + 1)
            env.progress.report "lake" { message := s!"Building {modules.size} modules · {tools.threads} CPUs", completed := ← get, total := some modules.size }
      catch error => abort.set true; throw error
    let outcome ← IO.ofExcept (← IO.wait task)
    unless ← cancellation.isRequested do
      let pending ← pending.atomically get
      match outcome with
      | .ok () =>
        unless pending.isEmpty do throw (IO.userError "Lake omitted module completions")
      | .error message =>
        -- A compiler/helper failure is a durable application result. Completed
        -- successes remain valid; missing modules carry the process diagnostics.
        if pending.isEmpty && !(← failures.get) then throw (IO.userError message)
        let diagnostics ← logs store directory
        for index in pending do
          let some m := modules[index]? | throw (IO.userError "Invalid pending module")
          publish { name := m.name, status := .failed, diagnostics, milliseconds := (← IO.monoMsNow) - start, message }
  finally
    abort.set true
    discard <| IO.wait task

/-- Keep all sources and installed artifacts in one worker-local workspace.
Restore the batch's shared prerequisite set once, in parallel; Lake uses the
worker's CPU budget and publications stream out as individual jobs finish. -/
def Tools.builder (tools : Tools) (store : ObjectStore) (env : Environment IO)
    (request : Request) (plan : Plan) : IO Unit := do
  let key ← workspaceKey tools request plan
  let cache := tools.cache.map fun cache => cache.directory.addExtension "workspace"
  Workspace.use store cache key fun session => do
    let directory := session.directory
    env.progress.report "build" { message := "Restoring sources", total := some plan.modules.size }
    let baseline ← restore tools store directory request plan #[] session
    let installed ← Std.Mutex.new (← IO.ofExcept (({} : Installed).remember baseline))
    let policy ← policyFile directory request
    Builders.run env plan fun cancellation modules inputs publish => do
      env.progress.report "lake" { message := s!"Restoring prerequisites for {modules.size} modules" }
      let previous ← installed.atomically get
      let missing ← inputs.filterM fun input => do
        let some ref := input.artifacts | throw (IO.userError "Missing prerequisite artifacts")
        return previous.modules[input.name]? != some ref
      let manifests ← Parallel.map tools.threads missing fun input => do
        let some ref := input.artifacts | throw (IO.userError "Missing prerequisite artifacts")
        session.readManifest ref
      let entries ← IO.ofExcept (Bundle.mergeMany manifests)
      let state ← IO.ofExcept (previous.remember entries)
      -- Identical artifacts can be packed differently on redelivery. Compare
      -- contents; never overwrite conflicting prerequisite bytes.
      Bundle.restore store directory (entries.filter fun e => !previous.files.contains e.path)
        request.limits.bytes tools.cache tools.threads
      installed.atomically (set { state with modules := missing.foldl (fun names (input : BuildResult) =>
        input.artifacts.map (names.insert input.name) |>.getD names) state.modules })
      unless ← cancellation.isRequested do
        buildBatch tools store env directory request policy session installed cancellation modules publish
    unless ← env.cancellation.isRequested do
      let inputs ← installed.atomically do return (← get).files.toArray.map (·.2)
      Bundle.validateInputs directory inputs tools.threads
      discard (Bundle.snapshot directory request.limits.bytes)
      session.commit

/-- Lake completes exactly the requested targets: native compilation, linking,
custom targets and any dynamic dependencies remain Lake's responsibility. -/
def Tools.finish (tools : Tools) (store : ObjectStore) (request : Request)
    (plan : Plan) (completed : Array BuildResult) (progress : ProgressReporter IO := .ignore) : IO BuildResult := do
  finishTargets tools store request plan completed progress

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
  let cache : Option Bundle.Cache ← match ← IO.getEnv "LEAN_BUILD_CACHE" with
    | none => pure none
    | some directory => do
      let value := (← IO.getEnv "LEAN_BUILD_CACHE_BYTES").getD "4294967296"
      let some bytes := value.toNat? | throw (IO.userError "Invalid LEAN_BUILD_CACHE_BYTES")
      pure (some { directory := directory, bytes : Bundle.Cache })
  return { toolchain := ← IO.FS.realPath toolchain, helper := ← IO.FS.realPath helper, cache }

def Tools.backend (tools : Tools) (store : ObjectStore) : Backend IO :=
  let configured := fun env : LeanCloud.Environment IO => { tools with threads := max 1 env.currentWorker.cpus, cancelled := env.cancellation.isRequested }
  { prepare := fun env => (configured env).prepare store
    start := Builders.seed
    builder := fun env => (configured env).builder store env
    results := Builders.results
    finish := fun env request plan completed => (configured env).finish store request plan completed env.progress }

end LeanBuild
