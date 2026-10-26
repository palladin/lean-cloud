import Lean
import Std.Sync.Mutex

namespace LeanCloudRuntime.StorageHttp
open Lean

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

def component (text : String) : String := String.ofList (text.toUTF8.data.toList.flatMap fun b =>
  let c := Char.ofNat b.toNat
  if b.toNat < 128 && (c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~') then [c]
  else ['%', hexDigit (b.toNat / 16), hexDigit b.toNat])

def form (fields : List (String × String)) : ByteArray :=
  (String.intercalate "&" (fields.map fun (key, value) => component key ++ "=" ++ component value)).toUTF8

structure Request where
  service : String
  url : String
  method : String := "GET"
  headers : Array (String × String) := #[]
  body : ByteArray := {}
  /-- libcurl's SigV4 service specification and access-key/secret pair. -/
  signing : Option (String × String × String) := none
  /-- Node-local credential endpoints must not send tokens through a proxy. -/
  noProxy : Bool := false

private opaque ClientType : NonemptyType
private def Client := ClientType.type
private instance : Nonempty Client := ClientType.property
@[extern "lc_http_client"] private opaque newClient : IO Client
@[extern "lc_http_storage"] private opaque transfer (client : @&Client)
  (url method : @&String) (headers : @&Array String) (body : @&ByteArray)
  (signing : @&Array String) (noProxy : Bool) : IO (UInt32 × ByteArray × Option Nat)

-- Exclusive checkout permits concurrent transfers without sharing a handle.
-- Only idle handles are bounded; active work is bounded by the caller's pool.
initialize idle : Std.Mutex (Array Client) ← Std.Mutex.new #[]

/-- In-process binary HTTP with reusable connections. Credentials are cleared
after each call; redirects are disabled and errors omit secrets and URLs. -/
def sendWithLength (request : Request) : IO (Nat × ByteArray × Option Nat) := do
  unless (request.url.startsWith "https://" || request.url.startsWith "http://") &&
      !request.url.contains '\x00' do throw (IO.userError "Storage requires an HTTP(S) endpoint")
  unless ["GET", "HEAD", "PUT", "POST", "DELETE"].contains request.method do
    throw (IO.userError "Invalid storage HTTP method")
  let mut headers := #[]
  for (name, value) in request.headers do
    unless !name.isEmpty && !name.contains ':' &&
        !(name ++ value).toList.any (fun c => c == '\r' || c == '\n' || c == '\x00') do
      throw (IO.userError "Invalid storage request header")
    headers := headers.push (name ++ ": " ++ value)
  let signing := request.signing.map (fun (service, access, secret) => #[service, access, secret]) |>.getD #[]
  unless signing.all (fun value => !value.contains '\x00') do
    throw (IO.userError "Invalid storage signing configuration")
  let client ← idle.atomically do
    let clients ← get
    if let some client := clients.back? then set clients.pop; return client
    newClient
  try
    let (status, body, length) ← transfer client request.url request.method headers request.body signing request.noProxy
    return (status.toNat, body, length)
  finally idle.atomically do
    if (← get).size < 32 then modify (·.push client)

def send (request : Request) : IO (Nat × ByteArray) := do
  let (status, body, _) ← sendWithLength request
  return (status, body)

/-- Credential response fields are simple text, never nested XML. Do not include
the document or field value in parse failures: both can contain credentials. -/
def xmlText (tag xml : String) : Except String String := do
  let [_, rest] := xml.splitOn ("<" ++ tag ++ ">") | throw s!"Invalid {tag} field"
  let [value, _] := rest.splitOn ("</" ++ tag ++ ">") | throw s!"Invalid {tag} field"
  unless !value.isEmpty && !value.contains '<' && !value.contains '&' do throw s!"Invalid {tag} field"
  return value

end LeanCloudRuntime.StorageHttp
