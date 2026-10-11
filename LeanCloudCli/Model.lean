import LeanCloudCli.Effects
import LeanCloudCli.Client
import LeanCloud.Program
import LeanCloud.Scheduler
import LeanCloud.Telemetry
import LeanCloud.Version

namespace LeanCloudCli
open Lean LeanCloud

def workerIndex? (role : String) : Option Nat := do
  unless role.startsWith "worker" do none
  let index ← (role.drop 6 |>.toString).toNat?
  if index > 0 && role == s!"worker{index}" then some (index - 1) else none

structure Deployment where
  project : String
  image : String
  programs : Array ProgramInfo

instance : ToJson Deployment where
  toJson value := Version.stamp "formatVersion" (Json.mkObj [
    ("project", toJson value.project), ("image", toJson value.image),
    ("programs", toJson value.programs)])

instance : FromJson Deployment where
  fromJson? json := do
    Version.check "formatVersion" "deployment" json
    return {
      project := ← json.getObjValAs? String "project"
      image := ← json.getObjValAs? String "image"
      programs := ← json.getObjValAs? _ "programs" }

structure Run where
  id : String
  image : String
  program : ProgramInfo
  input : Json

instance : ToJson Run where
  toJson value := Version.stamp "formatVersion" (Json.mkObj [
    ("id", toJson value.id), ("image", toJson value.image), ("program", toJson value.program),
    ("input", value.input)])

instance : FromJson Run where
  fromJson? json := do
    Version.check "formatVersion" "run manifest" json
    return {
      id := ← json.getObjValAs? String "id"
      image := ← json.getObjValAs? String "image"
      program := ← json.getObjValAs? _ "program"
      input := ← json.getObjVal? "input" }

def controlLabel : Pool.Mode → String
  | .active => "running"
  | .paused => "paused"
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

def readJson [FromJson α] (path : System.FilePath) : Cli α := do
  liftExcept (Json.parse (← request (.readFile path)) >>= fromJson?)

def saveJson [ToJson α] (path : System.FilePath) (value : α) : Cli Unit := do
  let temporary := path.toString ++ s!".{← request .pid}.tmp"
  request (.writeFile temporary (toJson value).pretty)
  request (.rename temporary path)

def Context.connection (ctx : Context) : Cli (Option Client.Connection) := do
  let path := ctx.home / "connection.json"
  unless ← request (.exists path) do return none
  let connection ← readJson (α := Client.Connection) path
  liftExcept connection.validate
  return some connection

def Context.requireConnection (ctx : Context) : Cli Client.Connection := do
  let some connection ← ctx.connection
    | throw "Not connected. Use 'connect NAME URL --token-file FILE' (or --token-env VARIABLE)."
  return connection

end LeanCloudCli
