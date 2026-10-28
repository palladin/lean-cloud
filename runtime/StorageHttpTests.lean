import LeanCloudRuntime.Storage
import LeanCloudCli.Http
import LeanCloudTests.Support
import Std.Http

namespace StorageHttpTests
open Lean LeanCloudRuntime LeanCloudTests Std.Http

private structure Service where
  objects : Std.Mutex (Array (String × ByteArray))
  requests : Std.Mutex (Array (String × String))
  peers : Std.Mutex (Array String)

private instance : Server.Handler Service where
  onRequest service request := do
    let path := toString request.line.uri.path
    let verb := toString request.line.method
    service.requests.atomically (modify (·.push (verb, path)))
    let attempts ← service.requests.atomically do return ((← get).filter (·.2 == path)).size
    if let some peer := request.extensions.get Server.RemoteAddr then
      service.peers.atomically (modify (·.push (toString peer)))
    let bytes : ByteArray ← request.body.readAll (maximumSize := some (8 * 1024 * 1024))
    if path == "/retry" || path == "/client-retry" then
      if attempts < 3 then
        return ← Response.new |>.status (if attempts == 1 then .serviceUnavailable else .tooManyRequests) |>.text "temporary"
      if path == "/client-retry" then
        let request ← IO.ofExcept (Json.parse (String.fromUTF8! bytes))
        return ← Response.ok |>.text (LeanCloud.Version.response request (toJson (42 : Nat))).compress
      return ← Response.ok |>.text "recovered"
    if path == "/denied" then return ← Response.new |>.status .unauthorized |>.text "denied"
    if path == "/auth" then
      return ← Response.ok |>.text ((request.line.headers.get? (.mk "authorization")).map toString |>.getD "")
    if path == "/redirect" then
      return ← Response.new |>.status .temporaryRedirect |>.header! "Location" "/auth" |>.text "redirect"
    if path == "/echo" then
      -- An asynchronous delay lets concurrent callers overlap.
      Std.Async.sleep 20
      return Response.ok |>.body (← Body.Full.ofByteArray bytes)
    if verb == "PUT" then
      let inserted ← service.objects.atomically do
        if (← get).any (·.1 == path) then return false
        modify (·.push (path, bytes))
        return true
      -- The first write committed, but its successful response was lost.
      if path == "/bucket/lost-response" && inserted then
        return ← Response.new |>.status .serviceUnavailable |>.text "temporary"
      return ← Response.new |>.status (if inserted then .created else .preconditionFailed) |>.text ""
    let value ← service.objects.atomically do return ((← get).find? (·.1 == path)).map (·.2)
    let some value := value | return ← Response.notFound |>.text ""
    -- The HTTP server suppresses the body for HEAD but retains its size.
    return Response.ok |>.body (← Body.Full.ofByteArray value)

def run : IO Unit := do
  let service : Service := ⟨← Std.Mutex.new #[], ← Std.Mutex.new #[], ← Std.Mutex.new #[]⟩
  let server ← (Server.serve (.v4 ⟨.ofParts 127 0 0 1, 0⟩) service { enableKeepAlive := true }).block
  try
    let some (.v4 bound) := server.localAddr | throw (IO.userError "No storage test address")
    let url := s!"http://127.0.0.1:{bound.port}"
    let config : S3.Config := ⟨url, "bucket", "us-east-1", .keys "test-key" "test-secret" "", true⟩
    let store := S3.objects config
    let (_, recovered) ← StorageHttp.send { service := "test", url := url ++ "/retry" }
    assertEq (String.fromUTF8! recovered) "recovered"
    assertEq (← LeanCloudCli.Http.post (url ++ "/client-retry") "token" "{}") "42"
    let (denied, _) ← StorageHttp.send { service := "test", url := url ++ "/denied" }
    assertEq denied 401
    assertEq (← service.requests.atomically do return ((← get).filter (·.2 == "/denied")).size) 1
      "Authentication failure was retried"
    assertEq (← store.create "lost-response" "winner".toUTF8).data "winner".toUTF8.data
      "Retry after a committed write lost the canonical value"
    service.requests.atomically (set (#[] : Array (String × String)))
    service.peers.atomically (set (#[] : Array String))
    let bytes := ByteArray.mk ((Array.range 200003).map fun i => (i % 256).toUInt8)
    let ref ← store.putBytes bytes
    assertEq (← store.size ref.key) (some bytes.size)
    assertEq (← store.putBytes bytes) ref
    let names := (store.executionContextFor "test").blobs
    assertOutcome (← (names.publishNamed "file" ref).run) (.ok ref)
    let calls ← service.requests.atomically get
    assertEq (calls.filter (fun (verb, path) => verb == "GET" && path.endsWith ref.key)).size 0
      "Duplicate upload or name publication downloaded the content"
    let peers ← service.peers.atomically get
    assertTrue (peers.size == calls.size && peers.toList.eraseDups.length == 1)
      "Sequential transfers did not reuse the connection"
    let .ok downloaded ← (store.readBytes ref).run | throw (IO.userError "Binary download failed")
    assertEq downloaded.data bytes.data
    assertEq (← store.create "record" "winner".toUTF8).data "winner".toUTF8.data
    assertEq (← store.create "record" "loser".toUTF8).data "winner".toUTF8.data
      "Metadata create lost first-writer-wins semantics"
    assertOutcome (← (names.publishNamed "wrong-size" { ref with size := ref.size + 1 }).run)
      (.error ⟨.integrity, "Blob size does not match reference"⟩)
    let empty ← store.putBytes {}
    assertEq (← store.size empty.key) (some 0)
    assertEq (← store.putBytes {}) empty
    -- Size disagreement at a content key must never be silently accepted.
    service.objects.atomically (modify (·.map fun (key, value) =>
      (key, if key.endsWith empty.key then "bad".toUTF8 else value)))
    let rejected ← try discard <| store.putBytes {}; pure false catch _ => pure true
    assertTrue rejected "Conflicting content size was accepted"
    -- Reused handles must clear SigV4, bearer headers, method and request body.
    let request : StorageHttp.Request := { service := "test", url := url ++ "/auth", noProxy := true }
    let (_, signed) ← StorageHttp.send { request with signing := some ("aws:amz:us-east-1:s3", "new-key", "secret") }
    assertTrue ((String.fromUTF8! signed).startsWith "AWS4-HMAC-SHA256") "SigV4 header missing"
    let (_, bearer) ← StorageHttp.send { request with headers := #[("Authorization", "Bearer rotated")] }
    assertEq (String.fromUTF8! bearer) "Bearer rotated"
    let (_, cleared) ← StorageHttp.send request
    assertEq cleared.size 0 "Pooled handle leaked credentials to the next request"
    let (status, _) ← StorageHttp.send { request with url := url ++ "/redirect" }
    assertEq status 307 "Storage followed an unexpected redirect"
    let jobs ← (Array.range 8).mapM fun i => IO.asTask (do
      let payload := bytes.push i.toUInt8
      let (status, body) ← StorageHttp.send { request with url := url ++ "/echo", method := "POST", body := payload }
      assertEq status 200
      assertEq body.data payload.data "Concurrent transfer mixed binary bodies") .dedicated
    for job in jobs do IO.ofExcept (← IO.wait job)
    -- Same-sized corruption is still detected on reads, not trusted as content.
    service.objects.atomically (modify (·.map fun (key, value) =>
      (key, if key.endsWith ref.key then value.set! 0 255 else value)))
    assertError (← (store.readBytes ref).run) .integrity
    IO.println "Storage HTTP: binary transfers, pooled connections, credential reset, concurrent IO and content deduplication passed."
  finally server.shutdownAndWait.block

end StorageHttpTests
