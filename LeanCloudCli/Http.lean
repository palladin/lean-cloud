import Lean
import Std.Sync.Mutex

namespace LeanCloudCli.Http

private opaque ClientType : NonemptyType
private def Client := ClientType.type
private instance : Nonempty Client := ClientType.property

@[extern "lc_http_client"] private opaque newClient : IO Client
@[extern "lc_http_post"] private opaque postRaw (client : @&Client)
  (url token body : @&String) (timeoutMs : UInt32) : IO (UInt32 × String)

-- One reusable client per destination. A libcurl handle is never used
-- concurrently; separate destinations can proceed independently.
initialize clients : Std.Mutex (Array (String × Std.Mutex Client)) ← Std.Mutex.new #[]

def post (url token body : String) (timeoutMs : UInt32 := 30000) : IO String := do
  let client ← clients.atomically do
    if let some (_, client) := (← get).find? (·.1 == url) then return client
    let client ← Std.Mutex.new (← newClient)
    modify (·.push (url, client))
    return client
  let (status, response) ← client.atomically do postRaw (← get) url token body timeoutMs
  unless 200 ≤ status && status < 300 do
    throw (IO.userError s!"HTTP {status}: {response}")
  return response

end LeanCloudCli.Http
