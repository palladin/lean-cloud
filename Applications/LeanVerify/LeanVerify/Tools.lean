import LeanVerify.Workflow
import LeanVerify.Bundle
import LeanCloudRuntime.Process

namespace LeanVerify
open Lean LeanCloud LeanCloudRuntime

/-- Tool paths are deployment configuration, never workflow input. Repositories
are trusted executable code (Lake configuration and Lean metaprograms). -/
structure Tools where
  toolchain : System.FilePath
  helper : System.FilePath

private def withWorkspace (action : System.FilePath → IO α) : IO α :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    action directory

private def run (tools : Tools) (directory : System.FilePath) (limits : Limits)
    (label command : String) (args : Array String) : IO (Except String Unit) := do
  let home := directory / ".." / "home"
  IO.FS.createDirAll home
  let out ← Process.runFiles {
    -- env -i also works on macOS toolchains whose inheritEnv=false spawn fails.
    cmd := "/usr/bin/env", cwd := directory
    args := #["-i", s!"PATH={tools.toolchain / "bin"}:/usr/local/bin:/usr/bin:/bin",
      s!"HOME={home}", "LANG=C.UTF-8", "GIT_TERMINAL_PROMPT=0", "GIT_CONFIG_NOSYSTEM=1",
      "LAKE_NO_CACHE=true", "LAKE_ARTIFACT_CACHE=false", command] ++ args
  } (limits.seconds * 1000) (directory / ".." / s!"{label}.stdout")
    (directory / ".." / s!"{label}.stderr") (16 * 1024 * 1024)
  if out.stopped then return .error s!"{label}: time or output limit exceeded"
  if out.exitCode != 0 then return .error s!"{label} failed (exit {out.exitCode}): {out.stderr.takeEnd 4000}"
  return .ok ()

private def lake (tools : Tools) (directory : System.FilePath) (limits : Limits)
    (label : String) (args : Array String) : IO (Except String Unit) :=
  run tools directory limits label (tools.toolchain / "bin/lake").toString
    (#["--no-cache", "--keep-toolchain"] ++ args)

private def runHelper (tools : Tools) (directory : System.FilePath) (limits : Limits)
    (label : String) (args : Array String) : IO (Except String Unit) := do
  -- Loading Lean Lake configurations requires Lake's native metaprogram support.
  let library := tools.toolchain / "lib/lean" /
    (if System.Platform.isOSX then "libLake_shared.dylib" else "libLake_shared.so")
  lake tools directory limits label (#["env", "lean", s!"-M{limits.checkerMemoryMiB}",
    "--load-dynlib", library.toString, "--run", tools.helper.toString] ++ args)

private def logs (store : ObjectStore) (directory : System.FilePath) : IO FileRef := do
  let mut texts : Array String := #[]
  for entry in ← (directory / "..").readDir do
    if entry.fileName.endsWith ".stdout" || entry.fileName.endsWith ".stderr" then
      texts := texts.push s!"--- {entry.fileName} ---\n{← IO.FS.readFile entry.path}"
  Files.putText store (String.intercalate "\n" texts.toList)

private def readJson [FromJson α] (path : System.FilePath) : IO α := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)

private def verifyToolchain (tools : Tools) (directory : System.FilePath) : IO String := do
  let expected := (← IO.FS.readFile (directory / "lean-toolchain")).trimAscii.toString
  let version ← IO.Process.output { cmd := (tools.toolchain / "bin/lean").toString, args := #["--version"] }
  let release := (expected.splitOn ":v").getLast!
  unless expected == s!"leanprover/lean4:v{release}" && version.exitCode == 0 &&
      version.stdout.startsWith s!"Lean (version {release}," do
    throw (IO.userError s!"Project requires {expected}; deploy an image with that exact Lean toolchain")
  return expected

/-- Snapshot resolved sources once. The dependency manifest and package Git
revisions travel with them; prebuilt proof artifacts are excluded. -/
def Tools.prepareDirectory (tools : Tools) (store : ObjectStore) (request : Request)
    (directory : System.FilePath) (commit : String) : IO Preparation := do
  try
    let toolchain ← verifyToolchain tools directory
    let planned ← runHelper tools directory request.limits "plan"
      (#["plan", "../verify-plan.json", toString request.limits.modules] ++ request.modules)
    if let .error reason := planned then
      return { error := reason, diagnostics := ← logs store directory }
    let modules : Array Module ← readJson (directory / ".." / "verify-plan.json")
    IO.ofExcept (validateModules modules)
    -- Strip generated build products, including downloaded dependency caches.
    let source ← Bundle.capture store directory request.limits.bytes false
    return { plan := some { commit, toolchain, modules, source := ← Files.putJson store source } }
  catch error => return { error := toString error, diagnostics := ← logs store directory }

def Tools.prepare (tools : Tools) (store : ObjectStore) (request : Request) : IO Preparation :=
  withWorkspace fun directory => do
    let steps := #[
      ("git-init", #["init", "--quiet"]),
      ("git-remote", #["remote", "add", "origin", request.repository]),
      ("git-fetch", #["-c", "protocol.file.allow=never", "fetch", "--depth=1", "origin", request.revision]),
      ("git-checkout", #["checkout", "--detach", "--quiet", "FETCH_HEAD"]),
      ("git-revision", #["rev-parse", "HEAD"])]
    for (label, args) in steps do
      let result ← run tools directory request.limits label "git" args
      if let .error reason := result then
        return { error := reason, diagnostics := ← logs store directory }
    let commit := (← IO.FS.readFile (directory / ".." / "git-revision.stdout")).trimAscii.toString
    if ← (directory / ".gitmodules").pathExists then
      return { error := "Git submodules are not supported; use Lake dependencies" }
    tools.prepareDirectory store request directory commit

/-- Import only the transitive prerequisites of this module, never artifacts
from an unrelated ready branch. -/
def prerequisites (plan : Plan) (target : Module) : Array String := Id.run do
  let mut needed := target.imports
  for m in plan.modules.reverse do
    if needed.contains m.name then
      for dep in m.imports do
        unless needed.contains dep do needed := needed.push dep
  return needed

def Tools.check (tools : Tools) (store : ObjectStore) (request : Request)
    (plan : Plan) (module : Module) (completed : Array ModuleResult) : IO ModuleResult :=
  withWorkspace fun directory => do
    -- Blob transport errors propagate so the runtime can retry them.
    let source : Bundle.Manifest ← Files.readJson store plan.source
    Bundle.restore store directory source request.limits.bytes
    let needed := prerequisites plan module
    let mut imports : Bundle.Manifest := #[]
    for result in completed do
      if !needed.contains result.name then continue
      let some ref := result.artifacts | throw (IO.userError "Missing checked prerequisite artifacts")
      imports ← IO.ofExcept (Bundle.merge imports (← Files.readJson store ref))
    Bundle.restore store directory imports request.limits.bytes
    let result ← try
      unless (← verifyToolchain tools directory) == plan.toolchain do
        throw (IO.userError "Toolchain changed since preparation")
      -- Lake supplies the project's flags and builds tactic/plugin prerequisites.
      let build ← lake tools directory request.limits "build" #["build", s!"+{module.name}:olean"]
      if let .error reason := build then throw (IO.userError reason)
      IO.FS.writeFile (directory / ".." / "verify-policy.json") (toJson request).pretty
      let checked ← runHelper tools directory request.limits "check"
        #["check", module.name, "../verify-policy.json", "../verify-checked.json"]
      if let .error reason := checked then throw (IO.userError reason)
      let theorems : Array Theorem ← readJson (directory / ".." / "verify-checked.json")
      pure (.ok theorems : Except String (Array Theorem))
    catch error => pure (.error (toString error))
    let diagnostics ← logs store directory
    match result with
    | .error message => return { name := module.name, status := .failed, message, diagnostics }
    | .ok theorems =>
      let artifacts ← try
        pure (.ok (← Bundle.capture store directory request.limits.bytes true imports))
      catch error => pure (.error (toString error) : Except String Bundle.Manifest)
      match artifacts with
      | .error message => return { name := module.name, status := .failed, message, diagnostics }
      | .ok manifest => return {
          name := module.name, status := .checked, diagnostics, theorems
          artifacts := ← Files.putJson store manifest }

/-- Both paths are installed by the deployment image. Host tests can provide them. -/
def Tools.fromEnvironment : IO Tools := do
  let toolchain := (← IO.getEnv "LEAN_VERIFY_TOOLCHAIN").getD "/opt/verify-lean"
  let helper := (← IO.getEnv "LEAN_VERIFY_HELPER").getD "/opt/lean-verify/Helper.lean"
  return { toolchain := ← IO.FS.realPath toolchain, helper := ← IO.FS.realPath helper }

def Tools.backend (tools : Tools) (store : ObjectStore) : Backend IO :=
  ⟨tools.prepare store, tools.check store⟩

end LeanVerify
