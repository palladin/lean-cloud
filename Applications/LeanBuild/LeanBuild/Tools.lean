import LeanBuild.Workflow
import LeanBuild.Project
import LeanBuild.Bundle
import LeanBuild.Workspace
import LeanBuild.Toolchain
import LeanBuild.Builders
import LeanBuild.Watchdog
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
  /-- When false, the caller enforces `limits.seconds` through `cancelled`. -/
  deadline : Bool := true

/-- A persistent session's watchdog replaces its wall-clock deadline. -/
private def unbounded : Nat := 1 <<< 62

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
  } (if tools.deadline then limits.seconds * 1000 else unbounded) (directory / ".." / s!"{label}.stdout")
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

/-- Only the handler accesses files, invokes Git/Lake, or publishes bytes. -/
private def prepareHandle (tools : Tools) (store : ObjectStore) (request : Request)
    (directory : System.FilePath) : Project.PrepareOp α → IO α
  | .fetch => do
    let steps := #[
      ("git-init", #["init", "--quiet"]),
      ("git-remote", #["remote", "add", "origin", request.repository]),
      ("git-fetch", #["-c", "protocol.file.allow=never", "fetch", "--depth=1", "origin", request.revision]),
      ("git-checkout", #["checkout", "--detach", "--quiet", "FETCH_HEAD"]),
      ("git-revision", #["rev-parse", "HEAD"])]
    for (label, args) in steps do
      IO.ofExcept (← run tools directory request.limits label "git"
        (#["-c", s!"pack.threads={max 1 tools.threads}", "-c", s!"index.threads={max 1 tools.threads}"] ++ args))
    return (← IO.FS.readFile (directory / ".." / "git-revision.stdout")).trimAscii.toString
  | .hasSubmodules => (directory / ".gitmodules").pathExists
  | .checkProject => do
    let root ← IO.FS.realPath directory
    let cwd ← IO.FS.realPath (project directory request)
    unless cwd == root || cwd.toString.startsWith (root.toString ++ "/") do
      throw (IO.userError "Project directory is outside the repository")
    verifyToolchain tools cwd
  | .discover => do
    let policy ← policyFile directory request
    let output := directory / ".." / "build-plan.json"
    IO.ofExcept (← runHelper tools directory request "plan"
      #["plan", policy.toString, output.toString, directory.toString])
    readJson output
  | .snapshot => Bundle.snapshot directory request.limits.bytes
  | .platform => platform
  | .publish snapshot => do
    let source ← snapshot.publish store tools.cache (Builders.ioConcurrency tools.threads)
    Files.putJson store source (Builders.ioConcurrency tools.threads)
  | .diagnostics => logs store directory

private def runProject (handle : {α : Type} → op α → IO α) (program : Project.Program op α) : IO α := do
  IO.ofExcept (← Project.runWith (fun operation => do
    try return .ok (← handle operation) catch error => return .error error.toString) program)

def Tools.prepareDirectory (tools : Tools) (store : ObjectStore) (request : Request)
    (directory : System.FilePath) (commit : String) : IO Preparation :=
  runProject (prepareHandle tools store request directory) (Project.prepareDirectory commit)

def Tools.prepare (tools : Tools) (store : ObjectStore) (request : Request) : IO Preparation :=
  withWorkspace fun directory => runProject (prepareHandle tools store request directory) Project.prepare

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

private def finishHandle (tools : Tools) (store : ObjectStore) (request : Request)
    (plan : Plan) (session : Workspace.Session) (progress : ProgressReporter IO) : Project.FinishOp α → IO α
  | .now => IO.monoMsNow
  | .progress text => progress.report "finalize" { message := text }
  | .manifests refs => Parallel.map (Builders.ioConcurrency tools.threads) refs session.readManifest
  | .restore imports => restore tools store session.directory request plan imports session
  | .targets => do
    let directory := session.directory
    let policy ← policyFile directory request
    let output := directory / ".." / "built-modules.json"
    IO.ofExcept (← runHelper tools directory request "build" #["build", policy.toString, output.toString])
    readJson output
  | .difference baseline => Bundle.delta session.directory request.limits.bytes baseline #[] tools.threads
  | .diagnostics => logs store session.directory
  | .publish difference => do
    let changes ← difference.changed.publish store tools.cache (Builders.ioConcurrency tools.threads)
    let artifacts := difference.retained ++ changes
    let reference ← Bundle.publishManifest store artifacts (Builders.ioConcurrency tools.threads)
    session.rememberManifest reference artifacts
    return reference
  | .commit => session.commit

private def finishTargets (tools : Tools) (store : ObjectStore) (request : Request)
    (plan : Plan) (completed : Array BuildResult) (progress : ProgressReporter IO) : IO BuildResult := do
  let key ← workspaceKey tools request plan
  let cache := tools.cache.map fun cache => cache.directory.addExtension "workspace"
  Workspace.use store cache key (concurrency := Builders.ioConcurrency tools.threads) fun session =>
    runProject (finishHandle tools store request plan session progress) (Project.finish completed)

private structure Installed where
  modules : Std.HashMap String FileRef := {}
  installing : Std.HashMap String (FileRef × IO.Promise (Except IO.Error Unit)) := {}
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
private def installModule (tools : Tools) (store : ObjectStore) (directory : System.FilePath)
    (request : Request) (session : Workspace.Session) (installed : Std.Mutex Installed)
    (stop : CancellationToken IO) (input : BuildResult) (ref : FileRef) : IO Unit := do
  if ← stop.isRequested then return
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

/-- Share manifest reads and installation, not just pack transfers. Waiters do
not consume an IO permit, leaving capacity for other missing prerequisites. -/
private def install (tools : Tools) (store : ObjectStore) (directory : System.FilePath)
    (request : Request) (session : Workspace.Session) (installed : Std.Mutex Installed)
    (limit : Parallel.Limit) (stop : CancellationToken IO) (inputs : Array BuildResult) : IO Unit := do
  -- Filter cache hits before allocating a task pool.
  let missing ← installed.atomically do
    let state ← get
    return inputs.filter fun input => input.artifacts.isNone || state.modules[input.name]? != input.artifacts
  discard <| Parallel.map (Builders.ioConcurrency tools.threads) missing fun input => do
    if ← stop.isRequested then return
    let some ref := input.artifacts | throw (IO.userError "Missing prerequisite artifacts")
    let entry ← installed.atomically do
      let s ← get
      if s.modules[input.name]? == some ref then return none
      if let some (other, pending) := s.installing[input.name]? then
        unless other == ref do throw (IO.userError "Conflicting module artifacts")
        return some (pending, false)
      let pending ← IO.Promise.new
      set { s with installing := s.installing.insert input.name (ref, pending) }
      return some (pending, true)
    if let some (pending, owner) := entry then
      if owner then
        let outcome ← (limit.run (installModule tools store directory request session installed stop input ref)).toBaseIO
        installed.atomically (modify fun s => { s with installing := s.installing.erase input.name })
        pending.resolve outcome
      IO.ofExcept (← IO.wait pending.result!)

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
    let pending ← IO.mkRef (#[] : Array (Nat × Module × Nat))
    let watchdog ← Watchdog.create (request.limits.seconds * 1000)
    let finishing ← IO.mkRef false
    -- The session lasts as long as this worker's share of the build, so
    -- `limits.seconds` bounds inactivity instead: while modules wait in Lake or
    -- the session is finishing, the next completion must arrive in time.
    let stalled := watchdog.check
      (do return !(← pending.get).isEmpty || (← finishing.get))
      (do (← pending.get).anyM fun (id, _, _) => (output / s!"{id}.json").pathExists)
    -- Give Lake the worker's thread budget; the helper separately limits module
    -- jobs. Even a single-CPU worker needs a job thread plus the admission loop.
    let localTools := { tools with
      threads := max 2 env.currentWorker.cpus
      deadline := false
      cancelled := do return (← abort.atomically get) || (← env.cancellation.isRequested) || (← stalled) }
    let task ← IO.mkRef (none : Option (Task (Except IO.Error (Except String Unit))))
    let running := do
      let some task ← task.get | throw (IO.userError "Lake session has not started")
      pure task
    let next ← IO.mkRef (0 : Nat)
    let failed ← IO.mkRef false
    let cancel : IO Unit := do
      abort.atomically (set true)
      if let some task ← task.get then discard <| IO.wait task
    let engine : Builders.Engine (ModuleCompletion × Nat) := {
      start := fun cpus => do
        if (← task.get).isSome then throw (IO.userError "Lake session already started")
        let started ← IO.asTask (runHelper { localTools with threads := max 2 cpus } directory request "modules"
          #["serve", toString (Builders.compilerSlots cpus),
            policy.toString, input.toString, output.toString, directory.toString]) .dedicated
        task.set (some started)
      prefetch := fun stop inputs => install tools store directory request session installed installing stop inputs
      prepare := fun stop _ inputs => install tools store directory request session installed installing stop inputs
      submit := fun mod => do
        let id ← next.get
        let path := input / s!"{id}.json"
        let temporary := path.addExtension "pending"
        IO.FS.writeFile temporary (toJson mod.name).compress
        IO.FS.rename temporary path
        let start ← IO.monoMsNow
        if (← pending.get).isEmpty then watchdog.progress
        pending.modify (·.push (id, mod, start))
        next.set (id + 1)
      poll := do
        let task ← running
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
          -- Invalidate any watchdog probe before removing its evidence of progress.
          watchdog.progress
          IO.FS.removeFile path
        pending.set waiting
        if exited then
          if ← watchdog.timedOut then
            throw (IO.userError s!"No module finished within limits.seconds ({request.limits.seconds} s)")
          match ← IO.ofExcept (← IO.wait task) with
          | .error message => throw (IO.userError message)
          | .ok () => throw (IO.userError "Lake session exited before finish")
        return results
      publish := fun _ mod (value, elapsed) => publishModule tools store directory request session installed mod value elapsed
      finish := do
        let task ← running
        unless (← pending.get).isEmpty do throw (IO.userError "Lake session has unfinished modules")
        watchdog.progress
        finishing.set true
        IO.FS.writeFile (input / "finish") ""
        let result ← IO.ofExcept (← IO.wait task)
        if ← watchdog.timedOut then
          throw (IO.userError s!"Lake session did not finish within limits.seconds ({request.limits.seconds} s)")
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
