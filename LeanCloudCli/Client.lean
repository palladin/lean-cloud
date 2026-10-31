import LeanCloudCli.Effects
import LeanCloud.DeploymentApi

namespace LeanCloudCli.Client
open Lean LeanCloud

/-- Profiles retain a credential reference, never its secret. Authentication is
resolved at request time so a rotated credential takes effect without reconnecting. -/
structure Connection where
  url : String
  deployment : String
  tokenEnv : String
  tokenFile : Option String := none
  deriving ToJson, FromJson, BEq, Repr

def validateUrl (url : String) : Except String Unit := do
  unless !url.toList.any (fun c => c.toNat ≤ 32 || c.toNat == 127 || c == '\\') &&
      !url.contains '@' && !url.contains '?' && !url.contains '#' do
    throw "Endpoint must be an HTTPS URL without credentials, a query, or a fragment"
  let rest := if url.startsWith "https://" then url.drop 8 |>.toString
    else if url.startsWith "http://" then url.drop 7 |>.toString else ""
  let authority := (rest.splitOn "/").head!
  unless !authority.isEmpty do throw "Endpoint must be an HTTPS URL"
  if url.startsWith "http://" then
    let loopback := ["localhost", "127.0.0.1", "[::1]"].any fun host =>
      authority == host || (authority.startsWith (host ++ ":") &&
        (authority.drop (host.length + 1) |>.toString.toNat?).any (fun port => 0 < port && port ≤ 65535))
    unless loopback do throw "HTTP is supported only for loopback endpoints; use HTTPS remotely"

def Connection.validate (connection : Connection) : Except String Unit := do
  validateUrl connection.url
  unless DeploymentApi.validId connection.deployment do throw "Invalid deployment identity"
  unless !connection.tokenEnv.isEmpty &&
      connection.tokenEnv.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_')) &&
      !connection.tokenEnv.toList.head!.isDigit do throw "Invalid credential environment variable"
  if let some path := connection.tokenFile then
    unless path.startsWith "/" && !path.toList.any (fun c => c.toNat < 32 || c.toNat == 127) do
      throw "Credential file must be an absolute path"

private def callWithToken (url token : String) (deployment : Option String)
    (operation : DeploymentApi.Request) : Cli (Except String (DeploymentApi.Response operation)) := do
  liftExcept (validateUrl url)
  liftExcept operation.validate
  unless !token.isEmpty && !token.contains '\r' && !token.contains '\n' do throw "Invalid deployment credential"
  let body := match deployment with
    | none => operation.encode
    | some id => operation.encode.setObjVal! "deployment" (toJson id)
  let url := if url.endsWith "/" then url.dropEnd 1 |>.toString else url
  let text ← request (.httpPost (url ++ "/deployment") token body.compress)
  let result : Except String Json ← liftExcept (Json.parse text >>= fromJson?)
  match result with
  | .error error => return .error error
  | .ok value => return .ok (← liftExcept (fromJson? value))

def credential (name : String) (file : Option String := none) : Cli String := do
  if let some path := file then
    -- A saved reference is authoritative: missing secrets must not silently
    -- switch to an unrelated ambient credential.
    return (← request (.readFile path)).trimAscii.toString
  let some token ← request (.getEnv name)
    | throw s!"Set {name} to this deployment's client credential"
  return token

/-- Connection establishes and remembers the server identity; subsequent calls
are bound to it so reusing an endpoint cannot redirect commands to another deployment. -/
def connect (url tokenEnv : String) (tokenFile : Option String := none) : Cli Connection := do
  let candidate : Connection := ⟨url, "unbound", tokenEnv, tokenFile⟩
  liftExcept candidate.validate
  let info ← liftExcept (← callWithToken url (← credential tokenEnv tokenFile) none .describe)
  unless info.apiVersion == DeploymentApi.version do throw "Unsupported deployment API version"
  let connection := { candidate with deployment := info.deployment }
  liftExcept connection.validate
  return connection

def exchange (connection : Connection) (operation : DeploymentApi.Request) : Cli (Except String (DeploymentApi.Response operation)) := do
  liftExcept connection.validate
  callWithToken connection.url (← credential connection.tokenEnv connection.tokenFile) (some connection.deployment) operation

def call (connection : Connection) (operation : DeploymentApi.Request) : Cli (DeploymentApi.Response operation) := do
  liftExcept (← exchange connection operation)

end LeanCloudCli.Client
