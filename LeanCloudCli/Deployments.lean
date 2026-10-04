import LeanCloudCli.Model

namespace LeanCloudCli.Deployments
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
    else throw "Set LEAN_CLOUD_HOME to an absolute directory for the deployment catalog"
  unless (System.FilePath.mk path).isAbsolute do throw "Deployment catalog directory must be absolute"
  return path

private def read (directory : System.FilePath) : Cli Catalog := do
  let path := directory / "deployments.json"
  unless ← request (.exists path) do return {}
  let catalog ← readJson (α := Catalog) path
  let mut names := #[]
  for entry in catalog.entries do
    validateId entry.project
    unless entry.project == entry.project.toLower && (System.FilePath.mk entry.root).isAbsolute do
      throw "Invalid deployment catalog entry"
    if names.contains entry.project then throw "Duplicate deployment name in catalog"
    names := names.push entry.project
  if let some selected := catalog.selected then
    unless names.contains selected do throw "Selected deployment is missing from catalog"
  return catalog

def load : Cli Catalog := do read (← home)

private def insert (catalog : Catalog) (ctx : Context) (select : Bool) : Cli Catalog := do
  validateId ctx.project
  unless ctx.project == ctx.project.toLower do throw "Deployment project must be lowercase"
  let root := (← request (.realPath ctx.root)).toString
  if let some existing := catalog.entries.find? (·.project == ctx.project) then
    unless existing.root == root do
      throw s!"Deployment '{ctx.project}' already belongs to {safe existing.root}. Use 'use {ctx.project}' or a different LEAN_CLOUD_PROJECT."
  let entry : Entry := ⟨ctx.project, root⟩
  return {
    entries := (catalog.entries.filter (·.project != ctx.project)).push entry
    selected := if select then some ctx.project else catalog.selected }

/-- Reserve the Docker project name before deployment; a failed build stays visible. -/
def remember (ctx : Context) (select := true) : Cli Unit := do
  let directory ← home
  request (.createDir directory)
  withLock (directory / "catalog.lock") do
    let catalog ← insert (← read directory) ctx select
    saveJson (directory / "deployments.json") catalog

/-- Import catalogs from this application directory, including deployments taken down. -/
def discover (ctx : Context) : Cli Unit := do
  let directory := ctx.root / ".lean-cloud"
  let mut projects := #[ctx.project]
  if ← request (.exists directory) then
    projects := projects ++ (← request (.readDir directory))
  for project in projects do
    if !validId project || project != project.toLower then continue
    let candidate : Context := ⟨ctx.root, project⟩
    if ← request (.exists (candidate.home / "deployment.json")) then
      let deployment ← readJson (α := Deployment) (candidate.home / "deployment.json")
      unless deployment.project == project do throw "Deployment context mismatch"
      remember candidate false

def select (name : String) : Cli Context := do
  validateId name
  let catalog ← load
  let some entry := catalog.entries.find? (·.project == name)
    | throw s!"Unknown deployment '{safe name}'. Use 'deployments' or 'open DIRECTORY'."
  unless ← request (.isDir entry.root) do
    throw s!"Deployment directory is missing: {safe entry.root}"
  remember entry.context
  return entry.context

/-- Explicit environment selection overrides the remembered deployment. -/
def initial (fallback : Context) : Cli Context := do
  if (← request (.getEnv "LEAN_CLOUD_PROJECT")).isSome then return fallback
  let result ← observing load
  let .ok catalog := result | do
    printError s!"Cannot read deployment selection; using {safe fallback.root.toString}. Use 'doctor' for details."
    return fallback
  if let some entry := catalog.entries.find? (fun e => some e.project == catalog.selected) then
    if ← request (.isDir entry.root) then return entry.context
    printError s!"Selected deployment directory is missing: {safe entry.root}; using {safe fallback.root.toString}."
  return fallback

end LeanCloudCli.Deployments
