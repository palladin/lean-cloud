import LeanCloudCli.Effects
import LeanCloud.Program
import LeanCloud.Scheduler
import LeanCloud.Telemetry

namespace LeanCloudCli
open Lean LeanCloud

def defaultWorkerCount : Nat := 3

def workerNames (count : Nat) : Array String :=
  (Array.range count).map fun i => s!"worker{i + 1}"

def workerIndex? (role : String) : Option Nat := do
  unless role.startsWith "worker" do none
  let index ← (role.drop 6 |>.toString).toNat?
  if index > 0 && role == s!"worker{index}" then some (index - 1) else none

def isActor (role : String) : Bool := role == "scheduler" || (workerIndex? role).isSome

def deploymentServices (workers := defaultWorkerCount) : Array String :=
  #["blobs", "scheduler"] ++ workerNames workers

def deploymentVolumes (workers := defaultWorkerCount) : Array String :=
  #["scheduler-data", "blob-data", "scheduler-mailbox-data"] ++
    (workerNames workers).map (· ++ "-mailbox-data")

/-- Defaults apply to absent fields, never to malformed values. -/
def jsonFieldD [FromJson α] (json : Json) (field : String) (fallback : α) : Except String α :=
  match json.getObjVal? field with
  | .ok value => fromJson? value
  | .error _ => pure fallback

structure Deployment where
  project : String
  image : String
  programs : Array ProgramInfo
  workers : Nat := defaultWorkerCount
  /-- Retired mailbox volumes remain durable and may be reused on a later grow. -/
  retainedWorkers : Nat := 0
  deriving ToJson

instance : FromJson Deployment where
  fromJson? json := do
    return {
      project := ← json.getObjValAs? String "project"
      image := ← json.getObjValAs? String "image"
      programs := ← json.getObjValAs? _ "programs"
      workers := ← jsonFieldD json "workers" defaultWorkerCount
      retainedWorkers := ← jsonFieldD json "retainedWorkers" 0 }

def Deployment.retainedCount (deployment : Deployment) : Nat :=
  max deployment.workers deployment.retainedWorkers

structure Run where
  id : String
  image : String
  program : ProgramInfo
  input : Json
  /-- Initial pool size; recorded events extend the roster when workers join. -/
  workers : Nat := defaultWorkerCount
  deriving ToJson

instance : FromJson Run where
  fromJson? json := do
    return {
      id := ← json.getObjValAs? String "id"
      image := ← json.getObjValAs? String "image"
      program := ← json.getObjValAs? _ "program"
      input := ← json.getObjVal? "input"
      workers := ← jsonFieldD json "workers" defaultWorkerCount }

/-- Intent is saved before requesting scheduler controls, so interrupted commands can be retried. -/
inductive RunControl where
  | active | pausing | paused | killing | killed
  deriving BEq, FromJson, ToJson

def RunControl.label : RunControl → String
  | .active => "running"
  | .pausing => "pausing (retry pause)"
  | .paused => "paused"
  | .killing => "killing (retry kill)"
  | .killed => "killed"

structure Context where
  root : System.FilePath
  project : String := "lean-cloud-console"

def Context.home (ctx : Context) := ctx.root / ".lean-cloud" / ctx.project
def Context.runs (ctx : Context) := ctx.home / "runs"
def Context.directory (ctx : Context) (id : String) := ctx.runs / id

def validId (id : String) : Bool :=
  !id.isEmpty && id.length ≤ 80 && id.toList.all (fun c =>
    c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_'))

def validateId (id : String) : Cli Unit :=
  unless validId id do throw "IDs require 1–80 ASCII letters, digits, '-' or '_'"

/-- Keep the lock outside the removable deployment directory. Unlinking a held
lock would allow another console to create a new lock and enter concurrently. -/
def Context.withDeploymentLock (ctx : Context) (action : Cli α) : Cli α := do
  validateId ctx.project
  let directory := ctx.root / ".lean-cloud"
  request (.createDir directory)
  withLock (directory / s!".{ctx.project}.lock") action

/-- Escape all terminal controls in remote labels, code, and diagnostics. -/
def safe (value : String) : String := Styled.sanitize value

def clip (width : Nat) (value : String) : String :=
  let value := safe value
  if value.length ≤ width then value else String.ofList (value.toList.take (width - 1)) ++ "…"

def pad (width : Nat) (value : String) : String :=
  let value := clip width value
  value ++ String.ofList (List.replicate (width - value.length) ' ')

/-- A small shell tokenizer: quotes and escapes, never shell evaluation. -/
def words (line : String) : Except String (List String) := do
  let mut result := []
  let mut current := ""
  let mut quote : Option Char := none
  let mut escaped := false
  let mut started := false
  for c in line.toList do
    if escaped then
      current := current.push c; escaped := false; started := true
    else if c == '\\' && quote != some '\'' then escaped := true; started := true
    else if let some q := quote then
      if c == q then quote := none else current := current.push c
    else if c == '\'' || c == '"' then quote := some c; started := true
    else if c.isWhitespace then
      if started then result := result ++ [current]; current := ""; started := false
    else current := current.push c; started := true
  if escaped || quote.isSome then throw "Unclosed quote or escape"
  if started then result := result ++ [current]
  return result

def event? (line : String) : Option ExecutionEvent := do
  if !line.startsWith "@lean-cloud " then none else
    (Json.parse (line.drop 12 |>.toString) >>= fromJson?).toOption

def readJson [FromJson α] (path : System.FilePath) : Cli α := do
  liftExcept (Json.parse (← request (.readFile path)) >>= fromJson?)

def saveJson [ToJson α] (path : System.FilePath) (value : α) : Cli Unit := do
  let temporary := path.toString ++ s!".{← request .pid}.tmp"
  request (.writeFile temporary (toJson value).pretty)
  request (.rename temporary path)

end LeanCloudCli
