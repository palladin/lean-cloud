import LeanCloudRuntime.ObjectStore
import LeanCloudRuntime.Credentials

namespace LeanCloudRuntime.AzureBlob
open Lean LeanCloud

inductive Authentication where
  | file (path : String)
  | workload

instance : ToJson Authentication where
  toJson
    | .file path => Json.mkObj [("kind", toJson "file"), ("path", toJson path)]
    | .workload => Json.mkObj [("kind", toJson "workload")]

instance : FromJson Authentication where
  fromJson? json := do
    match ← json.getObjValAs? String "kind" with
    | "file" => return .file (← json.getObjValAs? _ "path")
    | "workload" => return .workload
    | _ => throw "Unknown Azure authentication kind"

structure Config where
  endpoint : String
  container : String
  authentication : Authentication
  deriving FromJson, ToJson

def Config.validate (config : Config) : Except String Unit := do
  unless config.endpoint.startsWith "https://" && !config.endpoint.endsWith "/" &&
      !config.endpoint.contains '?' && !config.endpoint.contains '#' do throw "Azure Blob requires an HTTPS endpoint"
  unless 3 ≤ config.container.length && config.container.length ≤ 63 &&
      config.container.toList.all (fun c => ('a' ≤ c && c ≤ 'z') || c.isDigit || c == '-') &&
      !config.container.startsWith "-" && !config.container.endsWith "-" &&
      (config.container.splitOn "--").length == 1 do throw "Invalid Azure blob container"
  if let .file path := config.authentication then
    unless !path.isEmpty do throw "Empty Azure credential path"

private def token (config : Config) : IO String := match config.authentication with
  | .file path => Credentials.readSecret path
  | .workload => Credentials.azureWorkload

def requestSpec (config : Config) (token method path : String) (body : ByteArray := {})
    (immutable := false) : StorageHttp.Request := {
  service := "Azure Blob", url := config.endpoint ++ "/" ++ config.container ++ path
  method, body
  headers := #[("Authorization", "Bearer " ++ token), ("x-ms-version", "2023-11-03")] ++
    (if method == "PUT" then #[("x-ms-blob-type", "BlockBlob")] else #[]) ++
    (if immutable then #[("If-None-Match", "*")] else #[]) }

private def request (config : Config) (method path : String) (body : ByteArray := {})
    (immutable := false) : IO (Nat × ByteArray) := do
  IO.ofExcept config.validate
  StorageHttp.send (requestSpec config (← token config) method path body immutable)

private def read (config : Config) (key : String) : IO (Option ByteArray) := do
  let (status, bytes) ← request config "GET" ("/" ++ key)
  if status == 404 then return none
  unless status == 200 do throw (IO.userError s!"Azure Blob read failed (HTTP {status})")
  return some bytes

private def size (config : Config) (key : String) : IO (Option Nat) := do
  IO.ofExcept config.validate
  let (status, _, length) ← StorageHttp.sendWithLength
    (requestSpec config (← token config) "HEAD" ("/" ++ key))
  if status == 404 then return none
  unless status == 200 do throw (IO.userError s!"Azure Blob metadata read failed (HTTP {status})")
  let some length := length | throw (IO.userError "Azure Blob response has no content length")
  return some length

private def putContent (config : Config) (key : String) (bytes : ByteArray) : IO Unit := do
  for _ in [:8] do
    let (status, _) ← request config "PUT" ("/" ++ key) bytes true
    if status == 201 then return
    unless status == 409 || status == 412 do
      throw (IO.userError s!"Azure Blob content upload failed (HTTP {status})")
    if let some length ← size config key then
      unless length == bytes.size do throw (IO.userError "Content-addressed blob size conflict")
      return
    IO.sleep 50
  throw (IO.userError "Azure Blob conditional upload did not settle")

private def create (config : Config) (key : String) (bytes : ByteArray) : IO ByteArray := do
  for _ in [:8] do
    let (status, _) ← request config "PUT" ("/" ++ key) bytes true
    if status == 201 then return bytes
    -- BlobAlreadyExists is 409; ConditionNotMet is 412. Neither overwrites.
    unless status == 409 || status == 412 do
      throw (IO.userError s!"Azure Blob creation failed (HTTP {status})")
    if let some existing ← read config key then return existing
    IO.sleep 50
  throw (IO.userError "Azure Blob conditional creation did not settle")

/-- Flat listings only. Runtime record names are ASCII and require no XML entity
decoding. Namespace validation happens above the provider before any deletion. -/
def listKeys (xml : String) : Except String (Array String) := do
  unless (xml.splitOn "<EnumerationResults").length == 2 &&
      (xml.splitOn "</EnumerationResults>").length == 2 do throw "Invalid Azure Blob listing"
  let blobs ← match xml.splitOn "<Blobs>" with
    | [_, rest] =>
      let [blobs, _] := rest.splitOn "</Blobs>" | throw "Invalid Azure Blob listing"
      pure blobs
    | _ =>
      unless (xml.splitOn "<Blobs />").length == 2 || (xml.splitOn "<Blobs/>").length == 2 do
        throw "Missing Azure Blob listing"
      pure ""
  let keys ← (blobs.splitOn "<Blob>").drop 1 |>.mapM fun item => do
    let [item, _] := item.splitOn "</Blob>" | throw "Invalid Azure Blob entry"
    StorageHttp.xmlText "Name" item
  unless (blobs.splitOn "<Name").length == keys.length + 1 do throw "Invalid Azure Blob names"
  return keys.toArray

def objects (config : Config) : ObjectStore where
  -- The provisioner owns container creation and permissions. Nodes only verify
  -- access, so starting a worker cannot silently create infrastructure.
  ensureContainer := do
    let (status, _) ← request config "GET" "?restype=container&comp=list&maxresults=1"
    unless status == 200 do throw (IO.userError s!"Azure Blob container unavailable (HTTP {status})")
  read := read config
  create := create config
  putContent := putContent config
  size := size config
  list keyPrefix := do
    let (status, bytes) ← request config "GET"
      ("?restype=container&comp=list&maxresults=128&prefix=" ++ StorageHttp.component keyPrefix)
    unless status == 200 do throw (IO.userError s!"Azure Blob listing failed (HTTP {status})")
    let some text := String.fromUTF8? bytes | throw (IO.userError "Invalid Azure Blob listing UTF-8")
    IO.ofExcept (listKeys text)
  erase key := do
    let (status, _) ← request config "DELETE" ("/" ++ key)
    unless status == 404 || status == 202 do throw (IO.userError s!"Azure Blob deletion failed (HTTP {status})")

end LeanCloudRuntime.AzureBlob
