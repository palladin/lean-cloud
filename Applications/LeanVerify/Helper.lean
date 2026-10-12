/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
The kernel replay below is adapted from Lean's LeanChecker.lean by Kim Morrison
and Sebastian Ullrich, under Apache 2.0; see LICENSE-LeanChecker.
Modifications: exact module selection, module planning and axiom policy checks.

Runs under the SOURCE project's exact toolchain, not the worker's toolchain.
   This file is shipped by LeanVerify and is never loaded from the repository. -/
import Lake
import Lake.Load
import Lean.Replay
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

private partial def axioms (env : Kernel.Environment) (name : Name)
    (seen : NameSet := {}) (found : NameSet := {}) : NameSet × NameSet := Id.run do
  if seen.contains name then return (seen, found)
  let mut seen := seen.insert name
  let some info := env.find? name | return (seen, found)
  let mut found := if info matches .axiomInfo _ then found.insert name else found
  let deps := info.type.getUsedConstants ++
    (info.value? true).toArray.flatMap Expr.getUsedConstants
  for dep in deps do
    (seen, found) := axioms env dep seen found
  return (seen, found)

/-- Recheck exactly one module, including its private declarations. This follows
Lean's bundled LeanChecker.replayFromImports, without its prefix selection. -/
private unsafe def checkModule (module : Name) (requested allowed : Array String) : IO Json := do
  let path ← findOLean module
  let mut files := #[path]
  if ← (path.addExtension "server").pathExists then
    files := files.push (path.addExtension "server")
    if ← (path.addExtension "private").pathExists then
      files := files.push (path.addExtension "private")
  let parts ← readModuleDataParts files
  let some (mod, _) := parts[0]? | throw (IO.userError "Empty module artifact")
  let some (fullMod, _) := parts.back? | throw (IO.userError "Empty module artifact")
  let (_, state) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport state mod.imports {} 0 false false (isModule := true)
  let mut constants := {}
  for name in fullMod.constNames, info in fullMod.constants do
    constants := constants.insert name info
  let checked ← env.toKernelEnv.replay constants
  let mut rows : Array Json := #[]
  for name in fullMod.constNames do
    let names := (axioms checked name).2.toArray.map Name.toString
    unless names.all allowed.contains do
      throw (IO.userError s!"{name} uses disallowed axioms: {names}")
    if requested.contains name.toString then
      unless (checked.find? name).any (fun c => c matches .thmInfo _) do
        throw (IO.userError s!"{name} is not a theorem")
      rows := rows.push (Json.mkObj [("name", toJson name.toString), ("axioms", toJson names)])
  return toJson rows

unsafe def main (args : List String) : IO UInt32 := do
  try
    match args with
    | "plan" :: output :: limit :: roots =>
      let ws ← workspace
      let mut done := #[]
      let mut rows := #[]
      for root in roots do
        (done, rows) ← visit ws root.toName [] done rows (limit.toNat?.getD 10000)
      IO.FS.writeFile output (toJson rows).pretty
    | ["check", module, policy, output] =>
      initSearchPath (← findSysroot)
      let json ← IO.ofExcept (Json.parse (← IO.FS.readFile policy))
      let requested : Array String ← IO.ofExcept (json.getObjValAs? _ "theorems")
      let allowed : Array String ← IO.ofExcept (json.getObjValAs? _ "allowedAxioms")
      IO.FS.writeFile output (← checkModule module.toName requested allowed).pretty
    | _ => throw (IO.userError "Expected plan OUTPUT LIMIT ROOT... or check MODULE POLICY OUTPUT")
    return 0
  catch error => IO.eprintln s!"{error}"; return 1
