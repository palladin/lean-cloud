import Lean

namespace LeanCloudRuntime.StorageHttp
open Lean

private def quote (text : String) : String :=
  "\"" ++ (text.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"
    |>.replace "\r" "\\r" |>.replace "\t" "\\t") ++ "\""

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

/-- Request headers and credentials are sent through stdin. Error messages
contain only the service and status, never response bodies, tokens, or URLs.
Redirects are deliberately disabled so credentials stay at the chosen endpoint. -/
def send (request : Request) : IO (Nat × ByteArray) :=
  IO.FS.withTempFile fun input inputPath => IO.FS.withTempFile fun _ outputPath => do
    unless request.url.startsWith "https://" || request.url.startsWith "http://" do
      throw (IO.userError "Storage requires an HTTP(S) endpoint")
    input.write request.body
    input.flush
    let mut options := "url = " ++ quote request.url ++ "\n"
    for (name, value) in request.headers do
      unless !name.isEmpty && !(name ++ value).toList.any (fun c => c == '\r' || c == '\n' || c == '\x00') do
        throw (IO.userError "Invalid storage request header")
      options := options ++ "header = " ++ quote (name ++ ": " ++ value) ++ "\n"
    if let some (service, access, secret) := request.signing then
      options := options ++ "aws-sigv4 = " ++ quote service ++ "\nuser = " ++ quote (access ++ ":" ++ secret) ++ "\n"
    let args := #["--disable", "--silent", "--show-error", "--connect-timeout", "10", "--max-time", "60",
      "--config", "-", "--request", request.method, "--output", outputPath.toString, "--write-out", "%{http_code}"] ++
      (if request.noProxy then #["--noproxy", "*"] else #[]) ++
      (if request.method == "PUT" || request.method == "POST" then #["--data-binary", "@" ++ inputPath.toString] else #[])
    let response ← IO.Process.output { cmd := "curl", args } (some options)
    unless response.exitCode == 0 do
      throw (IO.userError s!"{request.service} transport failed (curl {response.exitCode})")
    let some status := response.stdout.trimAscii.toString.toNat?
      | throw (IO.userError s!"{request.service} returned an invalid HTTP status")
    return (status, ← IO.FS.readBinFile outputPath)

/-- Credential response fields are simple text, never nested XML. Do not include
the document or field value in parse failures: both can contain credentials. -/
def xmlText (tag xml : String) : Except String String := do
  let [_, rest] := xml.splitOn ("<" ++ tag ++ ">") | throw s!"Invalid {tag} field"
  let [value, _] := rest.splitOn ("</" ++ tag ++ ">") | throw s!"Invalid {tag} field"
  unless !value.isEmpty && !value.contains '<' && !value.contains '&' do throw s!"Invalid {tag} field"
  return value

end LeanCloudRuntime.StorageHttp
