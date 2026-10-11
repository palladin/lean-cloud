import LeanCloudRuntime.StorageHttp
import Std.Sync.Mutex
import Std.Time

namespace LeanCloudRuntime.Credentials
open Lean

def now : IO Nat := do
  return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat

def expires (text : String) : Except String Nat := do
  let date ← (Std.Time.DateTime.parse text).mapError (fun _ => "Invalid credential expiration")
  return date.toTimestamp.toSecondsSinceUnixEpoch.val.toNat

structure Token (α : Type) where
  value : α
  expires : Nat

/-- Per-process credential cache. Refresh is serialized, rotated assertion files
are reread on refresh, and failed refreshes never cache an error or extend a lease. -/
abbrev Cache (α : Type) := Std.Mutex (Array (String × Token α))

def Cache.create : IO (Cache α) := Std.Mutex.new #[]

def Cache.acquire (cache : Cache α) (key : String) (clock : IO Nat)
    (fetch : IO (Token α)) : IO α := cache.atomically do
  let now ← clock
  if let some (_, token) := (← get).find? (fun (name, token) => name == key && now + 120 < token.expires) then
    return token.value
  let token ← fetch
  unless token.expires > (← clock) do throw (IO.userError "Cloud credentials have expired")
  modify fun entries => (entries.filter (fun (name, old) => name != key && now < old.expires)).push (key, token)
  return token.value

def environment (name : String) : IO String := do
  let some value ← IO.getEnv name | throw (IO.userError s!"Missing {name}")
  unless !value.isEmpty do throw (IO.userError s!"Empty {name}")
  return value

def readSecret (path : String) : IO String := do
  let value ← try IO.FS.readFile path catch _ => throw (IO.userError "Cannot read cloud credential file")
  let value := value.trimAscii.toString
  unless !value.isEmpty && value.utf8ByteSize ≤ 65536 do throw (IO.userError "Invalid cloud credential file")
  return value

structure Aws where
  accessKey : String
  secretKey : String
  sessionToken : String := ""

def Aws.decode (json : Json) : Except String (Token Aws) := do
  let access ← json.getObjValAs? String "AccessKeyId"
  let secret ← json.getObjValAs? String "SecretAccessKey"
  let token ← json.getObjValAs? String "SessionToken"
  let expiration ← json.getObjValAs? String "Expiration"
  unless !access.isEmpty && !secret.isEmpty && !token.isEmpty do throw "Empty AWS credentials"
  return ⟨⟨access, secret, token⟩, ← expires expiration⟩

def Aws.decodeXml (xml : String) : Except String (Token Aws) := do
  return ⟨⟨← StorageHttp.xmlText "AccessKeyId" xml, ← StorageHttp.xmlText "SecretAccessKey" xml,
    ← StorageHttp.xmlText "SessionToken" xml⟩, ← expires (← StorageHttp.xmlText "Expiration" xml)⟩

private initialize awsCache : Cache Aws ← Cache.create
private initialize azureCache : Cache String ← Cache.create

/-- EKS IRSA: the pod admission controller injects the role and projected JWT
file. Exchange it at the regional STS endpoint; no AWS CLI is needed in nodes. -/
def awsWorkload (region : String) : IO Aws := do
  unless !region.isEmpty && region.toList.all (fun c => c.isAlphanum || c == '-') do
    throw (IO.userError "Invalid AWS region")
  let role ← environment "AWS_ROLE_ARN"
  let path ← environment "AWS_WEB_IDENTITY_TOKEN_FILE"
  awsCache.acquire (region ++ "|" ++ role ++ "|" ++ path) now do
    let body := StorageHttp.form [
      ("Action", "AssumeRoleWithWebIdentity"), ("Version", "2011-06-15"),
      ("RoleArn", role), ("RoleSessionName", "lean-cloud"), ("DurationSeconds", "3600"),
      ("WebIdentityToken", ← readSecret path)]
    let (status, response) ← StorageHttp.send {
      service := "AWS identity", url := s!"https://sts.{region}.amazonaws.com/", method := "POST"
      headers := #[("Content-Type", "application/x-www-form-urlencoded")], body }
    unless status == 200 do throw (IO.userError s!"AWS identity exchange failed (HTTP {status})")
    let some xml := String.fromUTF8? response | throw (IO.userError "Invalid AWS identity response")
    IO.ofExcept ((Aws.decodeXml xml).mapError (fun _ => "Invalid AWS identity credentials"))

/-- Local development with `aws configure export-credentials --format process`.
Read on every request so a developer can replace the file without restarting. -/
def awsFile (path : String) : IO Aws := do
  let token ← IO.ofExcept ((Json.parse (← readSecret path) >>= Aws.decode).mapError
    (fun _ => "Invalid AWS credential file"))
  unless token.expires > (← now) do throw (IO.userError "AWS credential file has expired")
  return token.value

/-- AKS Workload Identity supplies these environment variables and rotates the
projected service-account JWT. Access tokens are scoped only to Azure Storage. -/
def azureWorkload : IO String := do
  let tenant ← environment "AZURE_TENANT_ID"
  let client ← environment "AZURE_CLIENT_ID"
  let path ← environment "AZURE_FEDERATED_TOKEN_FILE"
  unless tenant.toList.all (fun c => c.isAlphanum || c == '-') do throw (IO.userError "Invalid Azure tenant")
  azureCache.acquire (tenant ++ "|" ++ client ++ "|" ++ path) now do
    let started ← now
    let body := StorageHttp.form [
      ("grant_type", "client_credentials"), ("client_id", client),
      ("scope", "https://storage.azure.com/.default"),
      ("client_assertion_type", "urn:ietf:params:oauth:client-assertion-type:jwt-bearer"),
      ("client_assertion", ← readSecret path)]
    let (status, response) ← StorageHttp.send {
      service := "Azure identity", url := s!"https://login.microsoftonline.com/{tenant}/oauth2/v2.0/token"
      method := "POST", headers := #[("Content-Type", "application/x-www-form-urlencoded")], body }
    unless status == 200 do throw (IO.userError s!"Azure identity exchange failed (HTTP {status})")
    let parsed : Except String (Token String) := do
      let some text := String.fromUTF8? response | throw "Invalid encoding"
      let json ← Json.parse text
      let value ← json.getObjValAs? String "access_token"
      let duration ← json.getObjValAs? Nat "expires_in"
      unless !value.isEmpty && duration > 0 do throw "Invalid token"
      return ⟨value, started + duration⟩
    IO.ofExcept (parsed.mapError (fun _ => "Invalid Azure identity credentials"))

end LeanCloudRuntime.Credentials
