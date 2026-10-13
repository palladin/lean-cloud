/- Runs under the SOURCE project's exact toolchain, not the worker's toolchain.
   This file is shipped by LeanVerify and is never loaded from the repository.
   It plans and exports modules; the separate `lake check` process verifies them. -/
import Lake
import Lake.Load
import LeanExport.Basic
import Lean.Util.CollectAxioms
import Lean.Elab.ParseImportsFast

open Lean Lake System

private def workspace : IO Workspace := do
  let (elan?, lean?, lake?) ← findInstall?
  let some lean := lean? | throw (IO.userError "Lean installation not found")
  let some lake := lake? | throw (IO.userError "Lake installation not found")
  let env ← IO.ofExcept (← (Lake.Env.compute lake lean elan? (some true)).toBaseIO)
  let cfg : LoadConfig := {
    lakeEnv := env
    wsDir := ← IO.currentDir
    updateToolchain := false }
  let some ws ← (loadWorkspace cfg).toBaseIO
    | throw (IO.userError "Cannot load Lake workspace")
  let root := (← IO.FS.realPath (← IO.currentDir)).toString
  for pkg in ws.packages do
    let path := (← IO.FS.realPath pkg.dir).toString
    unless path == root || path.startsWith (root ++ "/") do
      throw (IO.userError "Lake dependency is outside the repository snapshot")
  return ws

private partial def visit (ws : Workspace) (name : Name) (active : List Name)
    (done : Array Name) (rows : Array Json) (limit : Nat) : IO (Array Name × Array Json) := do
  if done.contains name then return (done, rows)
  if active.contains name then throw (IO.userError s!"Import cycle: {name}")
  unless done.size + active.length < limit do throw (IO.userError "Module limit exceeded")
  let some mod := ws.findTargetModule? name | throw (IO.userError s!"Unknown source module: {name}")
  let root := (← IO.FS.realPath (← IO.currentDir)).toString ++ "/"
  unless (← IO.FS.realPath mod.leanFile).toString.startsWith root do
    throw (IO.userError s!"Source module outside snapshot: {name}")
  unless (mod.oleanFile.normalize.toString.splitOn "/.lake/build/").length > 1 do
    throw (IO.userError "LeanVerify currently requires the standard .lake/build artifact layout")
  let header ← Lean.parseImports' (← IO.FS.readFile mod.leanFile) mod.leanFile.toString
  let mut done := done
  let mut rows := rows
  let mut deps : Array String := #[]
  for imp in header.imports do
    if (ws.findModule? imp.module).isSome then
      deps := deps.push imp.module.toString
      (done, rows) ← visit ws imp.module (name :: active) done rows limit
    else
      -- Imports outside the workspace must come from the pinned toolchain.
      let path := (← findSysroot) / "lib" / "lean" / (imp.module.toString.replace "." "/" ++ ".olean")
      unless ← path.pathExists do throw (IO.userError s!"Unknown import: {imp.module}")
  let row := Json.mkObj [("name", toJson name.toString), ("imports", toJson deps)]
  return (done.push name, rows.push row)

/-- Explicit roots include safe private/internal declarations that the exporter's
default selection omits. Unsafe implementations are outside the exporter's scope. -/
private def exportModule (module : Name) (requested allowed : Array String)
    (exportPath output : String) : IO Unit := do
  let env ← importModules #[{ module }] {} (level := .private)
  let names := env.constants.toList.filterMap fun (name, info) =>
    if !info.isUnsafe &&
        (env.getModuleIdxFor? name).any (fun i => env.header.moduleNames[i.toNat]! == module)
    then some name else none
  let report : CoreM (Array Json) := do
    let mut rows := #[]
    for name in names do
      let axioms := (← collectAxioms name).map Name.toString
      unless axioms.all allowed.contains do
        throwError "{name} uses disallowed axioms: {axioms}"
      if requested.contains name.toString then
        unless (env.find? name).any (fun c => c matches .thmInfo _) do
          throwError "{name} is not a theorem"
        rows := rows.push (Json.mkObj [("name", toJson name.toString), ("axioms", toJson axioms)])
    return rows
  let (rows, _) ← Core.CoreM.toIO report { fileName := "", fileMap := default } { env }
  IO.FS.writeFile output (toJson rows).pretty
  IO.FS.withFile exportPath .write fun handle =>
    IO.withStdout (.ofHandle handle) (LeanExport.dumpEnv env (some names))

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | "plan" :: output :: limit :: roots =>
      let ws ← workspace
      let mut done := #[]
      let mut rows := #[]
      for root in roots do
        (done, rows) ← visit ws root.toName [] done rows (limit.toNat?.getD 10000)
      IO.FS.writeFile output (toJson rows).pretty
    | ["export", module, policy, exportPath, output] =>
      initSearchPath (← findSysroot)
      let json ← IO.ofExcept (Json.parse (← IO.FS.readFile policy))
      let requested : Array String ← IO.ofExcept (json.getObjValAs? _ "theorems")
      let allowed : Array String ← IO.ofExcept (json.getObjValAs? _ "allowedAxioms")
      exportModule module.toName requested allowed exportPath output
    | _ => throw (IO.userError "Expected plan OUTPUT LIMIT ROOT... or export MODULE POLICY EXPORT OUTPUT")
    return 0
  catch error => IO.eprintln s!"{error}"; return 1
