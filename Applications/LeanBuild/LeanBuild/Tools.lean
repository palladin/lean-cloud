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
    let source ← snapshot.publish store tools.cache (Builders.ioConcurrency tools.threads)
    let reference ← Files.putJson store source (Builders.ioConcurrency tools.threads)
    return { plan := some { commit, toolchain, platform, modules, source := reference } }

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
  Bundle.synchronize store directory workspace request.limits.bytes tools.cache (Builders.ioConcurrency tools.threads)
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
  Workspace.use store cache key (concurrency := Builders.ioConcurrency tools.threads) fun session => do
    let directory := session.directory
    let start ← IO.monoMsNow
    progress.report "finalize" { message := "Collecting artifact manifests" }
    let references ← completed.mapM fun result => do
      let some ref := result.artifacts | throw (IO.userError "Missing prerequisite artifacts")
      return ref
    let downloaded ← Parallel.map (Builders.ioConcurrency tools.threads) references session.readManifest
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
      let changes ← difference.changed.publish store tools.cache (Builders.ioConcurrency tools.threads)
      let artifacts := difference.retained ++ changes
      let reference ← Bundle.publishManifest store artifacts (Builders.ioConcurrency tools.threads)
      session.rememberManifest reference artifacts
      session.commit
      progress.report "finalize" { message := "Finished" }
      return { name := "targets", status := .built, diagnostics, milliseconds := (← IO.monoMsNow) - start, artifacts := some reference, builtModules }

private structure Installed where
  modules : Std.HashMap String FileRef := {}
  files : Std.HashMap String Bundle.Entry := {}
  transfers : Std.HashMap String (Task (Except IO.Error Unit)) := {}

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

/-- Reserve each immutable prerequisite path once. Other preparations await the
same transfer; conflicting bytes fail before installation. No lock spans IO. -/
private def install (tools : Tools) (store : ObjectStore) (directory : System.FilePath)
    (request : Request) (session : Workspace.Session) (installed : Std.Mutex Installed)
    (limit : Parallel.Limit) (stop : CancellationToken IO) (inputs : Array BuildResult) : IO Unit := do
  discard <| Parallel.map (Builders.ioConcurrency tools.threads) inputs fun input => limit.run do
    if ← stop.isRequested then return
    let some ref := input.artifacts | throw (IO.userError "Missing prerequisite artifacts")
    if (← installed.atomically do return (← get).modules[input.name]?) == some ref then return
    let manifest ← session.readManifest ref
    let transfers ← installed.atomically do
      let previous ← get
      let mut state ← IO.ofExcept (previous.remember manifest)
      let mut waiting := manifest.filterMap fun entry => previous.transfers[entry.path]?
      let missing := manifest.filter fun entry => !previous.files.contains entry.path
      unless missing.isEmpty do
        -- Restore a module's pack together, rather than re-reading the whole
        -- pack for each file. All overlapping preparations await this task.
        let task ← IO.asTask (Bundle.restore store directory missing
          request.limits.bytes tools.cache 1) .dedicated
        state := { state with transfers := missing.foldl (fun tasks entry => tasks.insert entry.path task) state.transfers }
        waiting := waiting.push task
      set state
      return waiting
    try
      for task in transfers do IO.ofExcept (← IO.wait task)
    finally
      for task in transfers do discard <| IO.wait task
    installed.atomically (modify fun s => { s with modules := s.modules.insert input.name ref })

private def publishModule (tools : Tools) (store : ObjectStore) (directory : System.FilePath)
    (request : Request) (session : Workspace.Session) (installed : Std.Mutex Installed)
    (mod : Module) (value : ModuleCompletion) (milliseconds : Nat) : IO BuildResult := do
  unless value.name == mod.name do throw (IO.userError "Module completion name mismatch")
  let diagnostics ← Files.putText store s!"{mod.name}\n{value.diagnostics}"
  if !value.success then
    return { name := mod.name, status := .failed, diagnostics, milliseconds, message := "Lake module compilation failed" }
  unless !value.paths.isEmpty && value.paths.all Bundle.safePath do
    throw (IO.userError "Invalid module artifact paths")
  let snapshot : Bundle.Snapshot := { root := directory, limit := request.limits.bytes, paths := value.paths }
  -- Keep a module's small files together. Parallelize modules and large pack
  -- chunks, without multiplying blob objects and cache scans for every file.
  let manifest ← snapshot.publish store tools.cache (Builders.ioConcurrency tools.threads) (packCount := 1)
  let artifacts ← Files.putJson store manifest (Builders.ioConcurrency tools.threads)
  installed.atomically do
    let state ← IO.ofExcept ((← get).remember manifest)
    set { state with modules := state.modules.insert mod.name artifacts }
  session.rememberManifest artifacts manifest
  return { name := mod.name, status := .built, artifacts, diagnostics, milliseconds, builtModules := #[mod.name] }

/-- The helper and workspace live for the whole builder. Numbered, atomically
renamed requests carry module names; independent completion files carry results.
This protocol crosses the project toolchain boundary without serializing jobs. -/
def Tools.builder (tools : Tools) (store : ObjectStore) (env : Environment IO)
    (request : Request) (plan : Plan) : IO Unit := do
  let store ← store.concurrent (Builders.ioConcurrency env.currentWorker.cpus)
  let key ← workspaceKey tools request plan
  let cache := tools.cache.map fun cache => cache.directory.addExtension "workspace"
  Workspace.use store cache key (concurrency := Builders.ioConcurrency tools.threads) fun session => do
    let directory := session.directory
    env.progress.report "worker" { message := "Restoring sources" }
    let baseline ← restore tools store directory request plan #[] session
    let installed ← Std.Mutex.new (← IO.ofExcept (({} : Installed).remember baseline))
    let installing ← Parallel.Limit.new (Builders.ioConcurrency tools.threads)
    let policy ← policyFile directory request
    let protocol := directory / ".." / "lake-session"
    if ← protocol.pathExists then IO.FS.removeDirAll protocol
    let input := protocol / "requests"
    let output := protocol / "results"
    IO.FS.createDirAll input
    IO.FS.createDirAll output
    let abort ← Std.Mutex.new false
    -- One helper thread can be occupied by the admission loop even on a
    -- single-CPU worker. The coordinator separately bounds compiler slots.
    let localTools := { tools with
      threads := max 2 env.currentWorker.cpus
      cancelled := do return (← abort.atomically get) || (← env.cancellation.isRequested) }
    let task ← IO.asTask (runHelper localTools directory request "modules"
      #["serve", policy.toString, input.toString, output.toString, directory.toString]) .dedicated
    let pending ← IO.mkRef (#[] : Array (Nat × Module × Nat))
    let next ← IO.mkRef (0 : Nat)
    let failed ← IO.mkRef false
    let cancel : IO Unit := do
      abort.atomically (set true)
      discard <| IO.wait task
    let engine : Builders.Engine (ModuleCompletion × Nat) := {
      prefetch := fun stop inputs => install tools store directory request session installed installing stop inputs
      prepare := fun stop _ inputs => install tools store directory request session installed installing stop inputs
      submit := fun mod => do
        let id ← next.get
        let path := input / s!"{id}.json"
        let temporary := path.addExtension "pending"
        IO.FS.writeFile temporary (toJson mod.name).compress
        IO.FS.rename temporary path
        let start ← IO.monoMsNow
        pending.modify (·.push (id, mod, start))
        next.set (id + 1)
      poll := do
        -- Unexpected helper termination is an exec error, not a node crash.
        let exited ← IO.hasFinished task
        let mut waiting := #[]
        let mut results := #[]
        for (id, mod, start) in ← pending.get do
          let path := output / s!"{id}.json"
          if !(← path.pathExists) then waiting := waiting.push (id, mod, start); continue
          let value : ModuleCompletion ← readJson path
          unless value.name == mod.name do throw (IO.userError "Module completion name mismatch")
          if !value.success then failed.set true
          results := results.push (mod.name, (value, (← IO.monoMsNow) - start))
          IO.FS.removeFile path
        pending.set waiting
        if exited then
          match ← IO.ofExcept (← IO.wait task) with
          | .error message => throw (IO.userError message)
          | .ok () => throw (IO.userError "Lake session exited before finish")
        return results
      publish := fun _ mod (value, elapsed) => publishModule tools store directory request session installed mod value elapsed
      finish := do
        unless (← pending.get).isEmpty do throw (IO.userError "Lake session has unfinished modules")
        IO.FS.writeFile (input / "finish") ""
        let result ← IO.ofExcept (← IO.wait task)
        if let .error message := result then
          unless ← failed.get do throw (IO.userError message)
      cancel }
    try
      Builders.run env plan engine
      unless ← env.cancellation.isRequested do
        let inputs ← installed.atomically do return (← get).files.toArray.map (·.2)
        Bundle.validateInputs directory inputs tools.threads
        discard (Bundle.snapshot directory request.limits.bytes)
        session.commit
    finally cancel

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
