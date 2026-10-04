import LeanCloudCli.Effects
import LeanCloud.Program
import LeanCloud.Scheduler
import LeanCloud.Telemetry

namespace LeanCloudCli
open Lean LeanCloud

structure Deployment where
  project : String
  image : String
  programs : Array ProgramInfo
  deriving FromJson, ToJson

structure Run where
  id : String
  image : String
  program : ProgramInfo
  input : Json
  deriving FromJson, ToJson

/-- Intent is saved before changing containers, so interrupted commands can be retried. -/
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
