import Lean

namespace LeanCloud.Version
open Lean

/-- The current wire and persistence format. Only this version is supported. -/
def current : Nat := 1

def check (field context : String) (json : Json) : Except String Unit := do
  let version ← json.getObjValAs? Nat field
  unless version == current do
    throw s!"Unsupported {context} version {version}; expected {current}."

def stamp (field : String) (json : Json) : Json := json.setObjVal! field (toJson current)

/-- All responses use the same versioned envelope, including errors. -/
def response (result : Json) : Json :=
  stamp "protocolVersion" (Json.mkObj [("result", result)])

def responsePayload (json : Json) : Except String Json := do
  check "protocolVersion" "HTTP protocol" json
  json.getObjVal? "result"

end LeanCloud.Version
