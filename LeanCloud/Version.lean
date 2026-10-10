import Lean

namespace LeanCloud.Version
open Lean

/-- Version 0 is the unversioned HTTP/SQLite format. Version 1 adds explicit
version markers and optional operational fields; existing payloads keep their
meaning. Broker-era storage is not part of this compatibility contract. -/
def current : Nat := 1

def check (field context : String) (json : Json) : Except String Unit := do
  let fields ← json.getObj?
  let version : Nat ← match fields[field]? with
    | none => pure 0
    | some value => fromJson? value
  unless version ≤ current do
    throw s!"Unsupported {context} version {version}; this binary supports up to {current}. Use a compatible binary; data was not migrated."

def stamp (field : String) (json : Json) : Json := json.setObjVal! field (toJson current)

/-- Keep the tagged result intact. Legacy callers receive the legacy shape. -/
def response (request result : Json) : Json :=
  if (request.getObjVal? "protocolVersion").isOk then
    stamp "protocolVersion" (Json.mkObj [("result", result)])
  else result

def responsePayload (json : Json) : Except String Json := do
  check "protocolVersion" "HTTP protocol" json
  if (json.getObjVal? "protocolVersion").isOk then json.getObjVal? "result"
  else pure json

end LeanCloud.Version
