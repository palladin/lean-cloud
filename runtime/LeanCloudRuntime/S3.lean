import LeanCloud.Worker

namespace LeanCloudRuntime.S3
open Lean LeanCloud

structure Config where
  endpoint : String
  bucket : String
  region : String := "us-east-1"
  accessKey : String
  secretKey : String
  deriving FromJson, ToJson

private def quote (text : String) : String :=
  "\"" ++ (text.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"
    |>.replace "\r" "\\r") ++ "\""

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

/-- Encode one path component, including slashes in user-supplied blob names. -/
def component (text : String) : String := String.ofList (text.toUTF8.data.toList.flatMap fun b =>
  let c := Char.ofNat b.toNat
  if b.toNat < 128 && (c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '~') then [c]
  else ['%', hexDigit (b.toNat / 16), hexDigit b.toNat])

private def request (config : Config) (method path : String) (body : ByteArray := {})
    (immutable := false) : IO (Nat × ByteArray) :=
  IO.FS.withTempFile fun input inputPath => IO.FS.withTempFile fun _ outputPath => do
    input.write body
    input.flush
    let url := config.endpoint ++ "/" ++ component config.bucket ++ path
    let args := #["--silent", "--show-error", "--connect-timeout", "10", "--max-time", "60",
      "--config", "-", "--aws-sigv4", s!"aws:amz:{config.region}:s3", "--request", method,
      "--url", url, "--output", outputPath.toString, "--write-out", "%{http_code}"] ++
      (if method == "PUT" then #["--data-binary", "@" ++ inputPath.toString] else #[]) ++
      (if immutable then #["--header", "If-None-Match: *"] else #[])
    -- Credentials go through stdin, not process arguments or diagnostic output.
    let credentials := "user = " ++ quote (config.accessKey ++ ":" ++ config.secretKey) ++ "\n"
    let response ← IO.Process.output { cmd := "curl", args } (some credentials)
    unless response.exitCode == 0 do
      throw (IO.userError s!"S3 transport failed (curl {response.exitCode})")
    let some status := response.stdout.trimAscii.toString.toNat?
      | throw (IO.userError "S3 returned an invalid HTTP status")
    return (status, ← IO.FS.readBinFile outputPath)

private def digest (bytes : ByteArray) : IO String := IO.FS.withTempFile fun handle path => do
  handle.write bytes
  handle.flush
  let result ← IO.Process.output { cmd := "openssl", args := #["dgst", "-sha256", "-r", path.toString] }
  let hash := (result.stdout.splitOn " ").head!
  unless result.exitCode == 0 && hash.length == 64 && hash.toList.all (fun c =>
      c.isDigit || ('a' ≤ c && c ≤ 'f')) do throw (IO.userError "SHA-256 computation failed")
  return hash

private def writeImmutable (config : Config) (path : String) (bytes : ByteArray) : IO Unit := do
  let (status, _) ← request config "PUT" path bytes true
  if status == 412 || status == 409 then
    let (readStatus, existing) ← request config "GET" path
    unless readStatus == 200 && existing == bytes do
      throw (IO.userError "S3 immutable object conflicts with existing contents")
  else unless 200 ≤ status && status < 300 do
    throw (IO.userError s!"S3 write failed (HTTP {status})")

def initializeBucket (config : Config) : IO Unit := do
  let (status, _) ← request config "PUT" ""
  unless (200 ≤ status && status < 300) || status == 409 do
    throw (IO.userError s!"S3 bucket initialization failed (HTTP {status})")

def putBytes (config : Config) (bytes : ByteArray) : IO BlobRef := do
  let key := "objects/" ++ (← digest bytes)
  writeImmutable config ("/" ++ key) bytes
  return ⟨key, bytes.size, modelChecksum bytes⟩

def readBytes (config : Config) (ref : BlobRef) : ExceptT CloudError IO ByteArray := do
  let hash := ref.key.drop 8 |>.toString
  unless ref.key.startsWith "objects/" && hash.length == 64 && hash.toList.all (fun c =>
      c.isDigit || ('a' ≤ c && c ≤ 'f')) do throw ⟨.integrity, "Invalid blob reference"⟩
  let (status, bytes) ← request config "GET" ("/" ++ ref.key)
  if status == 404 then throw ⟨.missingBlob, "Blob is missing"⟩
  unless status == 200 do liftM (m := IO) (throw (IO.userError s!"S3 read failed (HTTP {status})") : IO Unit)
  unless bytes.size == ref.size && modelChecksum bytes == ref.checksum && (← digest bytes) == hash do
    throw ⟨.integrity, "Blob contents do not match reference"⟩
  return bytes

/-- Hash names into flat keys: Unicode, slashes, and reserved URL characters
never depend on a provider's path normalization during request signing. Store
the original name alongside the reference and check it when resolving. -/
def name (config : Config) (name : String) (ref : BlobRef) : IO Unit := do
  writeImmutable config ("/names/" ++ (← digest name.toUTF8)) (toJson (name, ref)).compress.toUTF8

def resolve (config : Config) (name : String) : ExceptT CloudError IO BlobRef := do
  let (status, bytes) ← request config "GET" ("/names/" ++ (← digest name.toUTF8))
  if status == 404 then throw ⟨.missingBlob, "Blob name is missing"⟩
  unless status == 200 do liftM (m := IO) (throw (IO.userError s!"S3 name lookup failed (HTTP {status})") : IO Unit)
  let some text := String.fromUTF8? bytes | throw ⟨.codec, "Invalid blob name record"⟩
  match Json.parse text >>= fromJson? (α := String × BlobRef) with
  | .ok (storedName, ref) =>
    unless storedName == name do throw ⟨.integrity, "Blob name record does not match its key"⟩
    return ref
  | .error _ => throw ⟨.codec, "Invalid blob name record"⟩

def storage (config : Config) : BlobStorage Unit IO where
  putBlob bytes state := return (.ok (← putBytes config bytes), state)
  readBlob ref state := return (← (readBytes config ref).run, state)
  resolveBlob name state := return (← (resolve config name).run, state)

def connect (config : Config) : IO (Worker.Connection (BlobStorage Unit IO)) := do
  unless config.endpoint.startsWith "http://" || config.endpoint.startsWith "https://" do
    throw (IO.userError "S3 endpoint must use http or https")
  return ⟨storage config, pure ()⟩

end LeanCloudRuntime.S3
