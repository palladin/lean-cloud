/- Runs under the project's exact toolchain. Lake resolves target specifications,
   library membership and import dependencies; native/custom builds remain Lake jobs. -/
import Lake
import Lake.Load
import Lake.CLI.Build
import LeanExport.Basic
import Lean.Util.CollectAxioms

open Lean Lake System

private def readJson (path : String) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

private def workspace (policy : Json) : IO Workspace := do
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean? | throw (IO.userError "Lean installation not found")
  let some lake := lake? | throw (IO.userError "Lake installation not found")
  let cache : String ← IO.ofExcept (policy.getObjValAs? _ "cache")
  let env ← IO.ofExcept (← (Lake.Env.compute lake lean elan? (some (cache == "rebuild"))).toBaseIO)
  let options : Std.TreeMap String String ← IO.ofExcept (policy.getObjValAs? _ "options")
  let cfg : LoadConfig := {
    lakeEnv := env, wsDir := ← IO.currentDir, updateToolchain := false
    lakeOpts := options.toArray.foldl (fun map (key, value) => map.insert key.toName value) {} }
  let some ws ← (loadWorkspace cfg).toBaseIO
    | throw (IO.userError "Cannot load Lake workspace")
  return ws

private def inside (root path : FilePath) : IO Unit := do
  let root := (← IO.FS.realPath root).toString
  let path := (← IO.FS.realPath path).toString
  unless path == root || path.startsWith (root ++ "/") do
    throw (IO.userError "Source or Lake dependency is outside the repository snapshot")

private def targetModules (ws : Workspace) (cfg : BuildConfig) (key : BuildKey) : IO (Array Lake.Module) := do
  match key with
  | .facet target facet =>
    if facet == LeanLib.defaultFacet then
      if let .packageTarget pkg name := target then
        if let some lib := (ws.findPackageByKey? pkg).bind (·.findLeanLib? name) then
          -- A library can replace its default facets with arbitrary work.
          -- Delegate those defaults instead of forcing Lean compilation.
          if lib.defaultFacets != #[LeanLib.leanArtsFacet] then return #[]
    -- Source/query/custom facets need not elaborate the module at all. Only
    -- prebuild facets whose standard meaning includes Lean compilation.
    let supported := #[Module.leanArtsFacet, Module.oleanFacet, Module.ileanFacet,
      Module.cFacet, LeanLib.defaultFacet, LeanLib.leanArtsFacet,
      LeanExe.defaultFacet, LeanExe.exeFacet]
    if supported.contains facet then targetModules ws cfg target else return #[]
  | .module name =>
    let some m := ws.findTargetModule? name | throw (IO.userError s!"Unknown module: {name}")
    return #[m]
  | .packageModule pkg name =>
    let some p := ws.findPackageByKey? pkg | throw (IO.userError s!"Unknown package: {pkg}")
    let some m := p.findTargetModule? name | throw (IO.userError s!"Unknown module: {name}")
    return #[m]
  | .packageTarget pkg name =>
    let some p := ws.findPackageByKey? pkg | throw (IO.userError s!"Unknown package: {pkg}")
    if let some lib := p.findLeanLib? name then
      ws.runBuild lib.extraDep.fetch cfg
      return ← lib.getModuleArray
    if let some exe := p.findLeanExe? name then return #[exe.root]
    -- Opaque custom targets are executed by the final ordinary Lake build.
    return #[]
  | .package _ => return #[]

private partial def visit (root : FilePath) (limit : Nat) (mod : Lake.Module)
    (active : List Name) (done : Array Name) (rows : Array Json) : FetchM (Array Name × Array Json) := do
  if done.contains mod.name then return (done, rows)
  if active.contains mod.name then error s!"Import cycle: {mod.name}"
  unless done.size + active.length < limit do error "Module limit exceeded"
  -- Generated sources and declared native prerequisites must exist before reading imports.
  (← mod.lib.extraDep.fetch).await
  inside root mod.leanFile
  let imports ← (← mod.imports.fetch).await
  let mut done := done
  let mut rows := rows
  for dep in imports do
    (done, rows) ← visit root limit dep (mod.name :: active) done rows
  return (done.push mod.name, rows.push (Json.mkObj [
    ("name", toJson mod.name.toString), ("imports", toJson (imports.map (·.name.toString)))]))

private def plan (policy : Json) (output root : String) : IO Unit := do
  let ws ← workspace policy
  for pkg in ws.packages do inside root pkg.dir
  -- Rebuild starts from sources even if a repository committed build artifacts.
  -- Keep the resolved dependencies and generated inputs produced below.
  let cache : String ← IO.ofExcept (policy.getObjValAs? _ "cache")
  if cache == "rebuild" then
    -- Validate every directory before deleting any: a build directory must not
    -- contain another package (for example .lake, which also holds dependencies).
    for pkg in ws.packages do
      if ← pkg.buildDir.pathExists then
        inside root pkg.buildDir
        let output := (← IO.FS.realPath pkg.buildDir).toString
        for input in ws.packages do
          let input := (← IO.FS.realPath input.dir).toString
          if input == output || input.startsWith (output ++ "/") then
            throw (IO.userError "Build directory must not contain a package directory")
    ws.clean
  let cfg : BuildConfig := {}
  let targets : Array String ← IO.ofExcept (policy.getObjValAs? _ "targets")
  let specs ← (parseTargetSpecs ws targets.toList).toIO (IO.userError ∘ toString)
  let mut roots := #[]
  for spec in specs do
    unless spec.buildable do throw (IO.userError s!"Target is not buildable: {spec.info.key}")
    roots := roots ++ (← targetModules ws cfg spec.info.key)
  let limit : Nat ← IO.ofExcept (policy.getObjVal? "limits" >>= (·.getObjValAs? _ "modules"))
  let rows ← ws.runFetchM (do
    let mut done := #[]
    let mut rows := #[]
    for mod in roots do
      (done, rows) ← visit root limit mod [] done rows
    return rows) cfg
  IO.FS.writeFile output (toJson rows).pretty

/-- Run Lake's own target builder and retain the modules it actually fetched.
Scanning .olean files would also include unrelated, stale cache entries. -/
private def buildTargets (policy : Json) (output : String) : IO Unit := do
  let ws ← workspace policy
  let targets : Array String ← IO.ofExcept (policy.getObjValAs? _ "targets")
  let specs ← (parseTargetSpecs ws targets.toList).toIO (IO.userError ∘ toString)
  let names ← ws.runFetchM (do
    (← buildSpecs specs).await
    let store ← getThe BuildStore
    let mut names : Array String := #[]
    for ⟨key, _⟩ in store do
      match key with
      | .facet (.module name) facet | .facet (.packageModule _ name) facet =>
        if facet == Module.leanArtsFacet && !names.contains name.toString then
          names := names.push name.toString
      | _ => pure ()
    return names)
  let limit : Nat ← IO.ofExcept (policy.getObjVal? "limits" >>= (·.getObjValAs? _ "modules"))
  unless names.size ≤ limit do throw (IO.userError "Module limit exceeded after target build")
  IO.FS.writeFile output (toJson names).pretty

/-- One Lake context per cloud job: shared dependency jobs are fetched once and
Lake runs independent modules concurrently. Keep per-module failures as data;
the monitor still prints their diagnostics before the helper exits. -/
private def buildModules (policy : Json) (input output : String) : IO Unit := do
  let ws ← workspace policy
  let names : Array String ← IO.ofExcept (fromJson? (← readJson input))
  let outcomes ← IO.mkRef (none : Option (Array (String × Bool)))
  try
    ws.runFetchM do
      let jobs ← names.mapM fun name => do
        let some m := ws.findTargetModule? name.toName | error s!"Unknown module: {name}"
        return (name, ← m.leanArts.fetch)
      let rows ← jobs.mapM fun (name, job) => do
        let built := (← job.wait?).isSome
        return (name, built)
      outcomes.set (some rows)
  catch error =>
    -- Lake reports this after monitoring a failed module. Only accept it when
    -- our complete per-module results already account for that failure.
    let .userError "build failed" := error | throw error
    let some rows ← outcomes.get | throw error
    unless rows.any (fun row => !row.2) do throw error
  let some rows ← outcomes.get | throw (IO.userError "Missing module outcomes")
  IO.FS.writeFile output (toJson (rows.map fun (name, built) =>
    Json.mkObj [("name", toJson name), ("built", toJson built)])).pretty

/-- Export one combined environment, retaining safe private declarations and
checking requested theorem/axiom requirements. Shared dependencies are exported once. -/
private def exportModules (policy : Json) (modules : Array String)
    (exportPath output : String) : IO Unit := do
  unless !modules.isEmpty do throw (IO.userError "No built Lean modules to verify")
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map fun m => { module := m.toName }) {} (level := .private)
  let names := env.constants.toList.filterMap fun (name, info) =>
    if !info.isUnsafe && (env.getModuleIdxFor? name).any
        (fun i => modules.contains env.header.moduleNames[i.toNat]!.toString)
    then some name else none
  let requested : Array String ← IO.ofExcept (policy.getObjValAs? _ "theorems")
  let allowed : Array String ← IO.ofExcept (policy.getObjValAs? _ "allowedAxioms")
  let report : CoreM (Array Json) := do
    let mut rows := #[]
    for name in names do
      let axioms := (← collectAxioms name).map Name.toString
      unless axioms.all allowed.contains do throwError "{name} uses disallowed axioms: {axioms}"
      if requested.contains name.toString then
        unless (env.find? name).any (fun c => c matches .thmInfo _) do
          throwError "{name} is not a theorem"
        rows := rows.push (Json.mkObj [("name", toJson name.toString), ("axioms", toJson axioms)])
    let found := rows.filterMap (fun r => (r.getObjValAs? String "name").toOption)
    let missing := requested.filter (!found.contains ·)
    unless missing.isEmpty do throwError "Missing theorem(s): {missing}"
    return rows
  let (rows, _) ← Core.CoreM.toIO report { fileName := "", fileMap := default } { env }
  IO.FS.writeFile output (toJson rows).pretty
  IO.FS.withFile exportPath .write fun handle =>
    IO.withStdout (.ofHandle handle) (LeanExport.dumpEnv env (some names))

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["plan", policy, output, root] => plan (← readJson policy) output root
    | ["build", policy, output] => buildTargets (← readJson policy) output
    | ["modules", policy, input, output] => buildModules (← readJson policy) input output
    | ["export", policy, modules, exportPath, output] =>
      exportModules (← readJson policy) (← IO.ofExcept (fromJson? (← readJson modules))) exportPath output
    | _ => throw (IO.userError "Expected plan POLICY OUTPUT ROOT | build POLICY OUTPUT | modules POLICY INPUT OUTPUT | export POLICY MODULES EXPORT OUTPUT")
    return 0
  catch error => IO.eprintln s!"{error}"; return 1
