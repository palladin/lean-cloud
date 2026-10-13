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
  /-- This applies to the export checker only. Source builds still require trust. -/
  sandbox : Bool := true

private def withWorkspace (action : System.FilePath → IO α) : IO α :=
  IO.FS.withTempDir fun root => do
    let directory := root / "project"
    IO.FS.createDir directory
    action directory

private def run (tools : Tools) (directory : System.FilePath) (limits : Limits)
    (label command : String) (args : Array String)
    (files : Array (System.FilePath × Nat) := #[]) : IO (Except String Unit) := do
  let home := directory / ".." / "home"
  IO.FS.createDirAll home
  let out ← Process.runFiles {
    -- env -i also works on macOS toolchains whose inheritEnv=false spawn fails.
    cmd := "/usr/bin/env", cwd := directory
    args := #["-i", s!"PATH={tools.toolchain / "bin"}:/usr/local/bin:/usr/bin:/bin",
      s!"HOME={home}", "LANG=C.UTF-8", "GIT_TERMINAL_PROMPT=0", "GIT_CONFIG_NOSYSTEM=1",
      "LAKE_NO_CACHE=true", "LAKE_ARTIFACT_CACHE=false", command] ++ args
  } (limits.seconds * 1000) (directory / ".." / s!"{label}.stdout")
    (directory / ".." / s!"{label}.stderr") (16 * 1024 * 1024) files
  if out.stopped then return .error s!"{label}: time or output limit exceeded"
  if out.exitCode != 0 then
    return .error s!"{label} failed (exit {out.exitCode}): {out.stdout.takeEnd 2000}\n{out.stderr.takeEnd 4000}"
  return .ok ()

private def lake (tools : Tools) (directory : System.FilePath) (limits : Limits)
    (label : String) (args : Array String)
    (files : Array (System.FilePath × Nat) := #[]) : IO (Except String Unit) :=
  run tools directory limits label (tools.toolchain / "bin/lake").toString
    (#["--no-cache", "--keep-toolchain"] ++ args) files

private def runHelper (tools : Tools) (directory : System.FilePath) (limits : Limits)
    (label : String) (args : Array String)
    (files : Array (System.FilePath × Nat) := #[]) : IO (Except String Unit) := do
  -- Loading Lean Lake configurations requires Lake's native metaprogram support.
  let library := tools.toolchain / "lib/lean" /
    (if System.Platform.isOSX then "libLake_shared.dylib" else "libLake_shared.so")
  lake tools directory limits label (#["env", "lean", s!"-M{limits.checkerMemoryMiB}",
    "--load-dynlib", library.toString, "--run", tools.helper.toString] ++ args) files

/-- Verify an immutable export using the source toolchain's official checker.
No project artifacts are loaded into the checking process. No sandbox fallback. -/
def Tools.verifyExport (tools : Tools) (directory : System.FilePath) (limits : Limits)
    (exportPath : System.FilePath) (paranoid : Bool := false) : IO (Except String Unit) := do
  let args := #["check", s!"--from-export={exportPath}"] ++
    (if paranoid then #["--paranoid"] else #[]) ++
    (if tools.sandbox then #[] else #["--inadvisably-no-sandbox"])
  lake tools directory limits "check" args

private def logs (store : ObjectStore) (directory : System.FilePath) : IO FileRef := do
  let mut texts : Array String := #[]
  for entry in ← (directory / "..").readDir do
    if entry.fileName.endsWith ".stdout" || entry.fileName.endsWith ".stderr" then
      texts := texts.push s!"--- {entry.fileName} ---\n{← IO.FS.readFile entry.path}"
  Files.putText store (String.intercalate "\n" texts.toList)

private def readJson [FromJson α] (path : System.FilePath) : IO α := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson?)

/-- Accept stable source releases with `lake check`. The deployed toolchain must
still match the project exactly; this is a minimum version, not ABI compatibility. -/
def Tools.sourceRelease (toolchain : String) : Except String String := do
  let invalid := s!"LeanVerify requires a stable leanprover/lean4 release >= 4.35.0; project requires {toolchain}"
  let ["leanprover/lean4", release] := toolchain.splitOn ":v" | throw invalid
  let [major, minor, patch] := release.splitOn "." | throw invalid
  let some major := major.toNat? | throw invalid
  let some minor := minor.toNat? | throw invalid
  let some patch := patch.toNat? | throw invalid
  unless release == s!"{major}.{minor}.{patch}" &&
      (major > 4 || (major == 4 && minor >= 35)) do
    throw invalid
  return release

private def verifyToolchain (tools : Tools) (directory : System.FilePath) : IO String := do
  let expected := (← IO.FS.readFile (directory / "lean-toolchain")).trimAscii.toString
  let release ← IO.ofExcept (Tools.sourceRelease expected)
  let version ← IO.Process.output { cmd := (tools.toolchain / "bin/lean").toString, args := #["--version"] }
  unless version.exitCode == 0 &&
      version.stdout.startsWith s!"Lean (version {release}," do
    throw (IO.userError s!"Project requires {expected}; deploy an image with that exact Lean toolchain")
  return expected

/-- Snapshot resolved sources once. The dependency manifest and package Git
revisions travel with them; prebuilt proof artifacts are excluded. -/
def Tools.prepareDirectory (tools : Tools) (store : ObjectStore) (request : Request)
    (directory : System.FilePath) (commit : String) : IO Preparation := do
  let prepared : Except String (String × Array Module × Bundle.Snapshot) ← try
    let toolchain ← verifyToolchain tools directory
    let planned ← runHelper tools directory request.limits "plan"
      (#["plan", "../verify-plan.json", toString request.limits.modules] ++ request.modules)
    IO.ofExcept planned
    let modules : Array Module ← readJson (directory / ".." / "verify-plan.json")
    IO.ofExcept (validateModules modules)
    -- Strip generated build products, including downloaded dependency caches.
    let source ← Bundle.prepare directory request.limits.bytes false
    pure (.ok (toolchain, modules, source))
  catch error => pure (.error (toString error))
  match prepared with
  | .error reason => return { error := reason, diagnostics := ← logs store directory }
  | .ok (toolchain, modules, snapshot) =>
    -- Cloud.exec records publication exceptions as execution failures.
    let source ← snapshot.publish store
    return { plan := some { commit, toolchain, modules, source := ← Files.putJson store source } }

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
    -- Storage exceptions propagate to Cloud.exec; they are not proof rejections.
    let source : Bundle.Manifest ← Files.readJson store plan.source
    Bundle.restore store directory source request.limits.bytes
    let needed := prerequisites plan module
    let mut imports : Bundle.Manifest := #[]
    for result in completed do
      if !needed.contains result.name then continue
      let some ref := result.artifacts | throw (IO.userError "Missing checked prerequisite artifacts")
      imports ← IO.ofExcept (Bundle.merge imports (← Files.readJson store ref))
    Bundle.restore store directory imports request.limits.bytes
    let result : Except String (Array Theorem × Bundle.Snapshot) ← try
      unless (← verifyToolchain tools directory) == plan.toolchain do
        throw (IO.userError "Toolchain changed since preparation")
      -- Lake supplies the project's flags and builds tactic/plugin prerequisites.
      let build ← lake tools directory request.limits "build" #["build", s!"+{module.name}:olean"]
      if let .error reason := build then throw (IO.userError reason)
      IO.FS.writeFile (directory / ".." / "verify-policy.json") (toJson request).pretty
      let exportPath := directory / ".." / "verify.ndjson"
      let exported ← runHelper tools directory request.limits "export"
        #["export", module.name, "../verify-policy.json", exportPath.toString, "../verify-checked.json"]
        #[(exportPath, request.limits.bytes)]
      if let .error reason := exported then throw (IO.userError reason)
      let checked ← tools.verifyExport directory request.limits exportPath request.paranoid
      if let .error reason := checked then throw (IO.userError reason)
      let theorems : Array Theorem ← readJson (directory / ".." / "verify-checked.json")
      let artifacts ← Bundle.prepare directory request.limits.bytes true imports
      pure (.ok (theorems, artifacts))
    catch error => pure (.error (toString error))
    let diagnostics ← logs store directory
    match result with
    | .error message => return { name := module.name, status := .failed, message, diagnostics }
    | .ok (theorems, snapshot) =>
      let artifacts ← snapshot.publish store
      return {
        name := module.name, status := .checked, diagnostics, theorems
        exportFile := ← Files.upload store (directory / ".." / "verify.ndjson") request.limits.bytes
        artifacts := ← Files.putJson store artifacts }

/-- Both paths are installed by the deployment image. Host tests can provide them. -/
def Tools.fromEnvironment : IO Tools := do
  let toolchain := (← IO.getEnv "LEAN_VERIFY_TOOLCHAIN").getD "/opt/verify-lean"
  let helper := (← IO.getEnv "LEAN_VERIFY_HELPER").getD "/opt/lean-verify/Helper.lean"
  let sandbox ← match (← IO.getEnv "LEAN_VERIFY_SANDBOX").getD "1" with
    | "1" => pure true
    | "0" => pure false
    | _ => throw (IO.userError "LEAN_VERIFY_SANDBOX must be 0 or 1")
  return { toolchain := ← IO.FS.realPath toolchain, helper := ← IO.FS.realPath helper, sandbox }

def Tools.backend (tools : Tools) (store : ObjectStore) : Backend IO :=
  ⟨tools.prepare store, tools.check store⟩

end LeanVerify
