import LeanCloudRuntime.ObjectStore
import LeanCloudRuntime.Credentials

namespace LeanCloudRuntime.S3
open Lean LeanCloud

inductive Authentication where
  | keys (access secret token : String)
  | file (path : String)
  | workload

instance : ToJson Authentication where
  toJson
    | .keys access secret token => Json.mkObj [("kind", toJson "keys"), ("accessKey", toJson access),
        ("secretKey", toJson secret), ("sessionToken", toJson token)]
    | .file path => Json.mkObj [("kind", toJson "file"), ("path", toJson path)]
    | .workload => Json.mkObj [("kind", toJson "workload")]

instance : FromJson Authentication where
  fromJson? json := do
    match ← json.getObjValAs? String "kind" with
    | "keys" =>
      let token ← match (← json.getObj?)["sessionToken"]? with
        | none => pure "" | some value => fromJson? value
      return .keys (← json.getObjValAs? _ "accessKey") (← json.getObjValAs? _ "secretKey") token
    | "file" => return .file (← json.getObjValAs? _ "path")
    | "workload" => return .workload
    | _ => throw "Unknown S3 authentication kind"

structure Config where
  endpoint : String
  bucket : String
  region : String := "us-east-1"
  authentication : Authentication
  /-- Provisioners create cloud buckets. Local emulators can create on demand. -/
  provisioned : Bool := false
  deriving ToJson

instance : FromJson Config where
  fromJson? json := do
    let object ← json.getObj?
    let authentication : Authentication ← match object["authentication"]? with
      | some value => fromJson? value
      | none => Authentication.keys <$> json.getObjValAs? String "accessKey" <*>
          json.getObjValAs? String "secretKey" <*> pure ""
    return {
      endpoint := ← json.getObjValAs? _ "endpoint"
      bucket := ← json.getObjValAs? _ "bucket"
      region := ← match object["region"]? with | none => pure "us-east-1" | some value => fromJson? value
      provisioned := ← match object["provisioned"]? with | none => pure false | some value => fromJson? value
      authentication }

def Config.validate (config : Config) : Except String Unit := do
  unless (config.endpoint.startsWith "http://" || config.endpoint.startsWith "https://") &&
      !config.endpoint.endsWith "/" && !config.endpoint.contains '?' && !config.endpoint.contains '#' do
    throw "Invalid S3 endpoint"
  unless !config.bucket.isEmpty && config.bucket.toList.all (fun c =>
      c.toNat < 128 && (c.isAlphanum || c == '-' || c == '.' || c == '_')) do throw "Invalid S3 bucket"
  unless !config.region.isEmpty && config.region.toList.all (fun c =>
      c.toNat < 128 && (c.isAlphanum || c == '-')) do throw "Invalid S3 region"
  match config.authentication with
  | .keys access secret _ => unless !access.isEmpty && !secret.isEmpty do throw "Empty S3 credentials"
  | .file path => unless !path.isEmpty do throw "Empty AWS credential path"
  | .workload => unless config.endpoint.startsWith "https://" do throw "AWS workload identity requires HTTPS"

private def credentials (config : Config) : IO Credentials.Aws := do
  match config.authentication with
  | .keys access secret token => pure ⟨access, secret, token⟩
  | .file path => Credentials.awsFile path
  | .workload => Credentials.awsWorkload config.region

def requestSpec (config : Config) (keys : Credentials.Aws) (method path : String)
    (body : ByteArray := {}) (immutable := false) : StorageHttp.Request := {
  service := "S3", url := config.endpoint ++ "/" ++ StorageHttp.component config.bucket ++ path
  method, body, signing := some (s!"aws:amz:{config.region}:s3", keys.accessKey, keys.secretKey)
  headers := (if immutable then #[("If-None-Match", "*")] else #[]) ++
    (if keys.sessionToken.isEmpty then #[] else #[("x-amz-security-token", keys.sessionToken)]) }

private def request (config : Config) (method path : String) (body : ByteArray := {})
    (immutable := false) : IO (Nat × ByteArray) := do
  IO.ofExcept config.validate
  StorageHttp.send (requestSpec config (← credentials config) method path body immutable)

private def read (config : Config) (key : String) : IO (Option ByteArray) := do
  let (status, bytes) ← request config "GET" ("/" ++ key)
  if status == 404 then return none
  unless status == 200 do throw (IO.userError s!"S3 read failed (HTTP {status})")
  return some bytes

/-- A 409 can precede a visible winner. Retrying never overwrites an object. -/
private def create (config : Config) (key : String) (bytes : ByteArray) : IO ByteArray := do
  for _ in [:8] do
    let (status, _) ← request config "PUT" ("/" ++ key) bytes true
    if 200 ≤ status && status < 300 then return bytes
    unless status == 409 || status == 412 do
      throw (IO.userError s!"S3 creation failed (HTTP {status})")
    if let some existing ← read config key then return existing
    IO.sleep 50
  throw (IO.userError "S3 conditional creation did not settle")

/-- Decode the bounded URL-encoded listing. Consumers validate their namespace
before deletion; only ASCII keys generated by ObjectStore are used. -/
def listKeys (xml : String) : Except String (Array String) := do
  unless (xml.splitOn "<ListBucketResult").length == 2 && (xml.splitOn "</ListBucketResult>").length == 2 do
    throw "Invalid S3 listing"
  let [_, counts] := xml.splitOn "<KeyCount>" | throw "Missing S3 key count"
  let [count, _] := counts.splitOn "</KeyCount>" | throw "Invalid S3 key count"
  let some count := count.toNat? | throw "Invalid S3 key count"
  let keys ← (xml.splitOn "<Key>").drop 1 |>.mapM fun part => do
    let [key, _] := part.splitOn "</Key>" | throw "Invalid S3 key"
    return key.replace "%2F" "/" |>.replace "%2f" "/"
  unless keys.length == count do throw "S3 listing count does not match its keys"
  return keys.toArray

def objects (config : Config) : ObjectStore where
  ensureContainer := do
    if config.provisioned then
      let (status, _) ← request config "GET" "?list-type=2&max-keys=0"
      unless status == 200 do throw (IO.userError s!"S3 bucket unavailable (HTTP {status})")
      return
    let (status, _) ← request config "PUT" ""
    unless (200 ≤ status && status < 300) || status == 409 do
      throw (IO.userError s!"S3 bucket initialization failed (HTTP {status})")
  read := read config
  create := create config
  list keyPrefix := do
    let (status, bytes) ← request config "GET"
      ("?list-type=2&encoding-type=url&max-keys=128&prefix=" ++ StorageHttp.component keyPrefix)
    unless status == 200 do throw (IO.userError s!"S3 listing failed (HTTP {status})")
    let some text := String.fromUTF8? bytes | throw (IO.userError "Invalid S3 listing UTF-8")
    IO.ofExcept (listKeys text)
  erase key := do
    let (status, _) ← request config "DELETE" ("/" ++ key)
    unless status == 404 || (200 ≤ status && status < 300) do
      throw (IO.userError s!"S3 deletion failed (HTTP {status})")

end LeanCloudRuntime.S3
