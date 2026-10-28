import Lean
import LeanCloud.Version
import LeanCloud.Retry
import Std.Sync.Mutex

namespace LeanCloudCli.Http

private opaque ClientType : NonemptyType
private def Client := ClientType.type
private instance : Nonempty Client := ClientType.property

@[extern "lc_http_client"] private opaque newClient : IO Client
@[extern "lc_http_post"] private opaque postRaw (client : @&Client)
  (url token body : @&String) (timeoutMs : UInt32) : IO (Except UInt32 (UInt32 × String))
-- Exclusive checkout, without serializing every queue operation behind a slow
-- request. Idle handles retain connections; no lock spans network IO/backoff.
initialize clients : Std.Mutex (Array Client) ← Std.Mutex.new #[]

def post (url token body : String) (timeoutMs : UInt32 := 30000) : IO String := do
  let request ← IO.ofExcept (Lean.Json.parse body)
  IO.ofExcept (LeanCloud.Version.check "protocolVersion" "HTTP protocol" request)
  let body := (LeanCloud.Version.stamp "protocolVersion" request).compress
  let client ← clients.atomically do
    let idle ← get
    if let some client := idle.back? then set idle.pop; return client
    newClient
  let (status, response) ← try
    LeanCloud.Retry.http (postRaw client url token body timeoutMs) (·.1.toNat)
  finally clients.atomically do
    if (← get).size < 32 then modify (·.push client)
  unless 200 ≤ status && status < 300 do
    throw (IO.userError s!"HTTP {status}: {response}")
  return (← IO.ofExcept (Lean.Json.parse response >>= LeanCloud.Version.responsePayload)).compress

end LeanCloudCli.Http
