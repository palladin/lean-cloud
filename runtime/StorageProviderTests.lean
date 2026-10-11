import LeanCloudRuntime.Storage
import LeanCloudRuntime.Run
import LeanCloudTests.Support

namespace StorageProviderTests
open Lean LeanCloudRuntime LeanCloudTests

private def renewal : IO Unit := do
  let cache ← Credentials.Cache.create (α := Nat)
  let clock ← IO.mkRef 1000
  let calls ← IO.mkRef 0
  let fetch := do
    calls.modify (· + 1)
    IO.sleep 2
    return (⟨← calls.get, (← clock.get) + 500⟩ : Credentials.Token Nat)
  assertEq (← cache.acquire "one" clock.get fetch) 1
  assertEq (← cache.acquire "one" clock.get fetch) 1
  assertEq (← calls.get) 1 "Valid token was fetched again"
  clock.set 1381
  assertEq (← cache.acquire "one" clock.get fetch) 2 "Token was not refreshed before expiry"
  clock.set 1800
  let failed ← try
    discard <| cache.acquire "one" clock.get (throw (IO.userError "Unavailable"))
    pure false
    catch _ => pure true
  assertTrue failed "Refresh failure served the old token"
  assertEq (← cache.acquire "one" clock.get fetch) 3 "Refresh failure poisoned the cache"
  assertEq (← cache.acquire "two" clock.get fetch) 4 "Credentials crossed identities"
  clock.set 2300
  let tasks ← (Array.range 16).mapM fun _ => IO.asTask (cache.acquire "one" clock.get fetch) .dedicated
  for task in tasks do assertEq (← IO.ofExcept task.get) 5
  assertEq (← calls.get) 5 "Concurrent callers exchanged the same token repeatedly"
  let expired ← try
    discard <| cache.acquire "expired" clock.get (pure ⟨0, 1000⟩)
    pure false
    catch _ => pure true
  assertTrue expired "Expired exchange result entered the cache"

private def configuration : IO Unit := do
  for text in [include_str "../deploy/kubernetes/storage.azure.example.json",
      include_str "../deploy/kubernetes/storage.aws.example.json"] do
    let storage : Storage.Config ← unwrap (Json.parse text >>= fromJson?)
    discard <| unwrap storage.validate
  -- Runtime parsing stays independent of deployment tooling.
  let base ← unwrap (Json.parse (include_str "../deploy/config.json"))
  let runtime : Config ← unwrap (fromJson? base)
  let scheduler := runtime.localInbox none
  assertEq scheduler.mailboxes.scheduler.host "127.0.0.1"
  assertEq (toJson scheduler.mailboxes.workers) (toJson runtime.mailboxes.workers)
  let worker := runtime.localInbox (some "worker1")
  assertEq (toJson worker.mailboxes.scheduler) (toJson runtime.mailboxes.scheduler)
  assertEq (← unwrap (worker.mailboxes.worker "worker1")).host "127.0.0.1"
  assertEq (toJson (← unwrap (worker.mailboxes.worker "worker2")))
    (toJson (← unwrap (runtime.mailboxes.worker "worker2")))
  let json ← unwrap (Json.parse (include_str "../deploy/config.json"))
  let legacy : Config ← unwrap (fromJson? json)
  discard <| unwrap legacy.validate
  let .s3 s3 := legacy.blobs | throw (IO.userError "Legacy config changed provider")
  let aws : Storage.Config := .s3 { s3 with authentication := .workload, endpoint := "https://s3.eu-north-1.amazonaws.com", provisioned := true }
  let roundtrip : Storage.Config ← unwrap (fromJson? (toJson aws))
  assertEq (toJson roundtrip) (toJson aws)
  discard <| unwrap roundtrip.validate
  assertTrue (Storage.Config.validate (.s3 { s3 with authentication := .workload })).toOption.isNone
    "Workload credentials accepted an insecure endpoint"
  for value in [Json.null, toJson "unknown"] do
    let bad := (toJson aws).setObjVal! "provider" value
    assertTrue (fromJson? (α := Storage.Config) bad).toOption.isNone "Malformed provider silently selected S3"
  let azure : AzureBlob.Config := ⟨"https://account.blob.core.windows.net", "test-container", .workload⟩
  discard <| unwrap azure.validate
  let storage : Storage.Config ← unwrap (fromJson? (toJson (.azure azure : Storage.Config)))
  assertEq (toJson storage) (toJson (.azure azure : Storage.Config))
  for name in ["Aaa", "a", "../escape", "a--b", "-abc", "abc-"] do
    assertTrue ({ azure with container := name }.validate).toOption.isNone "Invalid container accepted"
  let request := AzureBlob.requestSpec azure "example-token" "PUT" "/runs/one/records/abc" "hello".toUTF8 true
  assertTrue (request.headers.contains ("If-None-Match", "*")) "Azure write may overwrite"
  assertTrue (request.headers.contains ("x-ms-blob-type", "BlockBlob")) "Missing block blob type"
  assertTrue (request.headers.contains ("Authorization", "Bearer example-token")) "Missing OAuth header"
  let request := S3.requestSpec s3 ⟨"key", "secret", "temporary-session"⟩ "PUT" "/object" {} true
  assertTrue (request.headers.contains ("If-None-Match", "*")) "S3 write may overwrite"
  assertTrue (request.headers.contains ("x-amz-security-token", "temporary-session")) "Temporary session token omitted"
  assertEq request.signing (some (s!"aws:amz:{s3.region}:s3", "key", "secret"))

private def parsing : IO Unit := do
  assertEq (← unwrap (Credentials.expires "1970-01-01T00:00:01Z")) 1
  assertTrue (Credentials.expires "wrong").toOption.isNone "Invalid expiration accepted"
  let key := "runs/one/records/" ++ String.ofList (List.replicate 64 'a')
  let xml := "<?xml version=\"1.0\"?><EnumerationResults ServiceEndpoint=\"example\"><Blobs><Blob><Name>" ++ key ++
    "</Name><Properties><Content-Length>0</Content-Length></Properties></Blob></Blobs><NextMarker /></EnumerationResults>"
  assertEq (← unwrap (AzureBlob.listKeys xml >>= ObjectStore.runRecordKeys "one")) #[key]
  for empty in ["<Blobs />", "<Blobs/>", "<Blobs></Blobs>"] do
    assertEq (← unwrap (AzureBlob.listKeys ("<EnumerationResults>" ++ empty ++ "</EnumerationResults>"))) #[]
  for broken in ["", "<EnumerationResults></EnumerationResults>", xml.replace "<Name>" "<Name Encoded=\"true\">",
      xml.replace "</Blob>" "", xml.replace "</EnumerationResults>" ""] do
    assertTrue (AzureBlob.listKeys broken).toOption.isNone "Malformed listing treated as empty or complete"
  assertTrue (AzureBlob.listKeys (xml.replace "runs/one/" "runs/other/") >>= ObjectStore.runRecordKeys "one").toOption.isNone
    "Azure listing escaped the run namespace"
  let credentials := "<Credentials><AccessKeyId>key</AccessKeyId><SecretAccessKey>secret</SecretAccessKey>" ++
    "<SessionToken>session+/=</SessionToken><Expiration>2999-01-01T00:00:00Z</Expiration></Credentials>"
  let parsed ← unwrap (Credentials.Aws.decodeXml credentials)
  assertEq parsed.value.sessionToken "session+/="
  assertTrue (Credentials.Aws.decodeXml (credentials.replace "</Expiration>" "")).toOption.isNone "Missing expiration accepted"
  IO.FS.withTempFile fun _ path => do
    let file (token : String) := Json.mkObj [("AccessKeyId", toJson "key"), ("SecretAccessKey", toJson "secret"),
      ("SessionToken", toJson token), ("Expiration", toJson "2999-01-01T00:00:00Z")]
    IO.FS.writeFile path (file "first").compress
    assertEq (← Credentials.awsFile path.toString).sessionToken "first"
    IO.FS.writeFile path (file "rotated").compress
    assertEq (← Credentials.awsFile path.toString).sessionToken "rotated" "Credential file was cached past rotation"
    IO.FS.writeFile path "sensitive-test-marker"
    let message ← try discard <| Credentials.awsFile path.toString; pure "" catch error => pure error.toString
    assertTrue (!message.isEmpty && (message.splitOn "sensitive-test-marker").length == 1) "Credential file leaked into diagnostics"

def run : IO Unit := do
  renewal
  configuration
  parsing
  IO.println "Cloud providers: credential renewal, concurrent refresh, file rotation, wire contracts, and listing validation passed."

end StorageProviderTests
