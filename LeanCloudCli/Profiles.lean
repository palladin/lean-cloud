import LeanCloudCli.Model

namespace LeanCloudCli.Profiles
open Lean

/-- A local index; execution state remains in the deployment's services. -/
structure Entry where
  project : String
  root : String
  deriving FromJson, ToJson, BEq, Repr

def Entry.context (entry : Entry) : Context := ⟨entry.root, entry.project⟩

structure Catalog where
  entries : Array Entry := #[]
  selected : Option String := none
  deriving FromJson, ToJson

def home : Cli System.FilePath := do
  let path ← if let some path ← request (.getEnv "LEAN_CLOUD_HOME") then pure path
    else if let some path ← request (.getEnv "XDG_STATE_HOME") then pure (path ++ "/lean-cloud")
    else if let some path ← request (.getEnv "HOME") then pure (path ++ "/.local/state/lean-cloud")
    else throw "Set LEAN_CLOUD_HOME to an absolute directory for the connection catalog"
  unless (System.FilePath.mk path).isAbsolute do throw "Connection catalog directory must be absolute"
  return path

private def read (directory : System.FilePath) : Cli Catalog := do
  let path := directory / "deployments.json"
  unless ← request (.exists path) do return {}
  let catalog ← readJson (α := Catalog) path
  let mut names := #[]
  for entry in catalog.entries do
    validateId entry.project
    unless entry.project == entry.project.toLower && (System.FilePath.mk entry.root).isAbsolute do
      throw "Invalid connection catalog entry"
    if names.contains entry.project then throw "Duplicate connection name in catalog"
    names := names.push entry.project
  if let some selected := catalog.selected then
    unless names.contains selected do throw "Selected connection is missing from catalog"
  return catalog

/-- Only saved HTTP connections belong in the client catalog. -/
def load : Cli Catalog := do
  let catalog ← read (← home)
  let entries ← catalog.entries.filterM fun entry =>
    request (.exists (entry.context.home / "connection.json"))
  return { entries, selected := catalog.selected.filter fun name => entries.any (·.project == name) }

private def insert (catalog : Catalog) (ctx : Context) (select : Bool) : Cli Catalog := do
  validateId ctx.project
  unless ctx.project == ctx.project.toLower do throw "Connection name must be lowercase"
  let root := (← request (.realPath ctx.root)).toString
  if let some existing := catalog.entries.find? (·.project == ctx.project) then
    unless existing.root == root do
      throw s!"Connection '{ctx.project}' already belongs to {safe existing.root}. Use 'use {ctx.project}' or a different connection name."
  let entry : Entry := ⟨ctx.project, root⟩
  return {
    entries := (catalog.entries.filter (·.project != ctx.project)).push entry
    selected := if select then some ctx.project else catalog.selected }

/-- Save a named HTTP connection and the selected profile. -/
def remember (ctx : Context) (select := true) : Cli Unit := do
  let directory ← home
  request (.createDir directory)
  withLock (directory / "catalog.lock") do
    let catalog ← insert (← load) ctx select
    saveJson (directory / "deployments.json") catalog

/-- A profile name must not claim another connection's cache directory. -/
def checkOwnership (ctx : Context) : Cli Unit := do
  discard <| insert (← load) ctx false

def select (name : String) : Cli Context := do
  validateId name
  let catalog ← load
  let some entry := catalog.entries.find? (·.project == name)
    | throw s!"Unknown connection '{safe name}'. Use 'connections' or 'connect NAME URL'."
  unless ← request (.isDir entry.root) do
    throw s!"Connection cache directory is missing: {safe entry.root}"
  remember entry.context
  return entry.context

/-- Restore the last selected HTTP connection without contacting the server. -/
def initial (fallback : Context) : Cli Context := do
  let result ← observing load
  let .ok catalog := result | do
    printError s!"Cannot read connection selection; using {safe fallback.root.toString}. Use 'doctor' for details."
    return fallback
  if let some entry := catalog.entries.find? (fun e => some e.project == catalog.selected) then
    if ← request (.isDir entry.root) then return entry.context
    printError s!"Connection cache directory is missing: {safe entry.root}; using {safe fallback.root.toString}."
  return fallback

end LeanCloudCli.Profiles
