/- Runs under the project's exact toolchain. Lake resolves target specifications,
   library membership and import dependencies; native/custom builds remain Lake jobs. -/
import Lake
import Lake.Load
import Lake.CLI.Build

open Lean Lake System

private def readJson (path : String) : IO Json := do
  IO.ofExcept (Json.parse (← IO.FS.readFile path))

/-- Lake parallelizes modules. Default each child compiler to one thread so
each does not independently create a hardware-sized pool. Weak arguments do
not change artifact traces; explicit project arguments can still override this. -/
private def compilerBudget (pkg : Package) : Package :=
  { pkg with config := { pkg.config with weakLeanArgs := #["-j1"] ++ pkg.config.weakLeanArgs } }

private def withCompilerBudget (ws : Workspace) : Workspace :=
  let packages := ws.packages.map compilerBudget
  { ws with
    packages
    packageMap := packages.foldl (fun map pkg => map.insert pkg.keyName pkg) {}
    size_packages_pos := by simpa [packages] using ws.size_packages_pos
    packages_wsIdx := by intro i h; simpa [packages, compilerBudget] using ws.packages_wsIdx (by simpa [packages] using h)
    depIdxs_packages := by
      intro pkg hp i hi
      obtain ⟨original, ho, rfl⟩ := Array.mem_map.mp hp
      simpa [packages] using ws.depIdxs_packages original ho i hi }

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
  return withCompilerBudget ws

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
    (active : List Name) (done : Std.HashSet Name) (rows : Array Json) : FetchM (Std.HashSet Name × Array Json) := do
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
  return (done.insert mod.name, rows.push (Json.mkObj [
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
    -- Start independent source scans together. Preserve generated-source
    -- prerequisites first; `visit` still determines the topological row order.
    let prerequisites ← roots.mapM fun mod => mod.lib.extraDep.fetch
    for job in prerequisites do job.await
    for mod in roots do
      inside root mod.leanFile
      discard mod.imports.fetch
    let mut done : Std.HashSet Name := {}
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

/-- Only this module's output paths are packed; completion never rescans the
whole source tree. Lake has finished writing these files before we report them. -/
private def modulePaths (m : Lake.Module) (root : String) : IO (Array String) := do
  let root := (← IO.FS.realPath root).toString ++ "/"
  let files := #[m.oleanFile, m.oleanServerFile, m.oleanPrivateFile, m.ileanFile,
    m.irFile, m.irSigFile, m.cFile, m.bcFile, m.traceFile, m.setupFile,
    m.coExportFile, m.coNoExportFile, m.bcoFile, m.dynlibFile]
  let files := files.flatMap fun path => #[path, path.addExtension "hash", path.addExtension "trace"]
  let mut paths : Array String := #[]
  for path in files do
    if ← path.pathExists then
      let path := (← IO.FS.realPath path).toString
      unless path.startsWith root do throw (IO.userError "Module output escaped the workspace")
      let relative := path.drop root.length |>.toString
      unless paths.contains relative do paths := paths.push relative
  unless ← m.oleanFile.pathExists do throw (IO.userError "Lake did not produce the module's olean")
  return paths


/-- One workspace and one BuildStore for the worker's lifetime. Requests and
completions are atomically renamed local files, so the helper can use the source
project's exact Lean version without sharing Lean values across processes.
Only this loop owns FetchM; jobs execute concurrently in Lake's task pool. -/
private def serveModules (policy : Json) (input output root : String) : IO Unit := do
  let ws ← workspace policy
  IO.FS.createDirAll output
  ws.runFetchM do
    let mut next := 0
    let mut seen : Std.HashSet String := {}
    let mut pending : Array (Nat × IO (Option Json)) := #[]
    repeat
      let mut waiting := #[]
      for (id, inspect) in pending do
        match ← inspect with
        | none => waiting := waiting.push (id, inspect)
        | some value =>
          let destination := FilePath.mk output / s!"{id}.json"
          let temporary := destination.addExtension "pending"
          IO.FS.writeFile temporary value.compress
          IO.FS.rename temporary destination
      pending := waiting
      let path := FilePath.mk input / s!"{next}.json"
      if ← path.pathExists then
        let name : String ← IO.ofExcept ((← readJson path.toString) |> fromJson?)
        unless !seen.contains name do error s!"Repeated module submission: {name}"
        let some m := ws.findTargetModule? name.toName | error s!"Unknown module: {name}"
        seen := seen.insert name
        let job ← m.leanArts.fetch
        let inspect : IO (Option Json) := do
          unless ← IO.hasFinished job.task do return none
          let (success, diagnostics) ← match ← job.wait with
            | .ok _ state => pure (true, state.log.toString)
            | .error _ state => pure (false, state.log.toString)
          let paths ← if success then modulePaths m root else pure #[]
          return some (Json.mkObj [
            ("name", toJson name), ("success", toJson success),
            ("paths", toJson paths), ("diagnostics", toJson diagnostics)])
        pending := pending.push (next, inspect)
        IO.FS.removeFile path
        next := next + 1
      else
        if pending.isEmpty && (← (FilePath.mk input / "finish").pathExists) then break
        IO.sleep 10

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["plan", policy, output, root] => plan (← readJson policy) output root
    | ["build", policy, output] => buildTargets (← readJson policy) output
    | ["serve", policy, input, output, root] => serveModules (← readJson policy) input output root
    | _ => throw (IO.userError "Expected plan POLICY OUTPUT ROOT | build POLICY OUTPUT | serve POLICY INPUT OUTPUT ROOT")
    return 0
  catch error => IO.eprintln s!"{error}"; return 1
