import LeanCloud.Program
import LeanCloud.Timing
import LeanCloud.Observations

/-! The client-facing deployment contract. Requests contain application data,
never host paths, executable arguments, mailbox routes or cloud credentials.
The same contract is used by local Docker, on-premise and cloud deployments. -/
namespace LeanCloud.DeploymentApi
open Lean LeanEff

def version : Nat := 1

/-- Node configuration only. Public responses never include this credential. -/
structure Access where
  deployment : String
  image : String
  token : String
  deriving ToJson, FromJson, BEq

structure Info where
  deployment : String
  image : String
  apiVersion : Nat := version
  deriving ToJson, FromJson

structure RunInfo where
  id : String
  entry : String
  input : Json
  resultSchema : String
  mode : Pool.Mode
  image : Option String := none
  /-- The source bundled at submission, not the currently deployed source. -/
  program : Option ProgramInfo := none
  deriving ToJson, FromJson

structure Page (α : Type) where
  items : Array α
  /-- Exclusive run-ID cursor. Pages are observations, not a catalog snapshot. -/
  next : Option String := none
  deriving ToJson, FromJson

/-- A live endpoint observation, not an execution lease or health guarantee. -/
structure Node where
  id : String
  online : Bool
  samples : Array ResourceSample := #[]
  warning : String := ""
  deriving ToJson, FromJson, Inhabited

structure ObservationPage extends Page Observations.Step where
  warning : String := ""
  deriving ToJson, FromJson

inductive Control where
  | pause | resume | kill
  deriving Repr, BEq, ToJson, FromJson

def Control.command (run : String) : Control → Pool.Command
  | .pause => .pause run
  | .resume => .resume run
  | .kill => .kill run

/-- Submission is idempotent by run ID and immutable definition. Other mutations
carry a caller-generated request ID, retained across ambiguous HTTP failures. -/
inductive Request where
  | describe
  | programs
  | runs (after : Option String := none) (limit : Nat := 50)
  | run (id : String)
  | submit (id entry : String) (input : Json)
  | control (requestId id : String) (action : Control)
  | remove (requestId id : String)
  | inspect (id : String)
  | outcome (id : String)
  | result (id : String)
  | nodes
  | observations (id worker : String) (after : Option String := none) (limit : Nat := 100)
  deriving ToJson, FromJson

abbrev Response : Request → Type
  | .describe => Info
  | .programs => Array ProgramInfo
  | .runs .. => Page RunInfo
  | .run .. => RunInfo
  | .submit .. => Unit
  -- A durable rejection is a response value. Transport/service failures remain
  -- outside it: only a confirmed receipt permits retiring the caller's ID.
  | .control .. | .remove .. => Except String Unit
  | .inspect .. => Timing.Status
  | .outcome .. => Option Exit
  | .result .. => String
  | .nodes => Array Node
  | .observations .. => ObservationPage

instance (request : Request) : ToJson (Response request) := by cases request <;> exact inferInstance
instance (request : Request) : FromJson (Response request) := by cases request <;> exact inferInstance

def validId (id : String) : Bool :=
  !id.isEmpty && id.length ≤ 80 && id.toList.all (fun c =>
    c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_'))

def Request.validate (request : Request) : Except String Unit := do
  let check (id : String) := unless validId id do throw "IDs require 1–80 ASCII letters, digits, '-' or '_'"
  match request with
  | .describe | .programs | .nodes => pure ()
  | .runs after limit =>
    unless 0 < limit && limit ≤ 100 do throw "Page size must be between 1 and 100"
    if let some after := after then check after
  | .control key id _ | .remove key id => check key; check id
  | .submit id entry _ =>
    check id
    unless !entry.isEmpty && entry.length ≤ 256 do throw "Invalid program entry"
  | .run id | .inspect id | .outcome id | .result id => check id
  | .observations id worker after limit =>
    check id; check worker
    unless 0 < limit && limit ≤ 100 do throw "Page size must be between 1 and 100"
    unless after.all (fun key => key.utf8ByteSize ≤ 4096) do throw "Invalid observation cursor"

def Request.encode (request : Request) : Json := Json.mkObj [
  ("apiVersion", toJson version), ("request", toJson request)]

/-- The public API requires its explicit version and validated request shape. -/
def Request.decode (json : Json) : Except String Request := do
  let actual ← json.getObjValAs? Nat "apiVersion"
  unless actual == version do throw s!"Unsupported deployment API version {actual}; expected {version}"
  let request ← json.getObjValAs? Request "request"
  request.validate
  return request

end LeanCloud.DeploymentApi
