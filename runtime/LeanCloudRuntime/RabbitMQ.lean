import LeanCloud.Worker

namespace LeanCloudRuntime.RabbitMQ
open Lean LeanCloud

structure Config where
  host : String
  port : Nat := 5672
  vhost : String := "/"
  user : String
  password : String
  queuePrefix : String := "lean-cloud."
  deriving FromJson, ToJson

private opaque HandleType : NonemptyType
def Handle := HandleType.type
instance : Nonempty Handle := HandleType.property

@[extern "lc_queue_open"]
private opaque openRaw (host : @&String) (port : UInt32) (vhost user password queue : @&String)
  (create consume : Bool) : IO Handle
@[extern "lc_queue_close"]
opaque Handle.close (handle : @&Handle) : IO Unit
@[extern "lc_queue_publish"]
private opaque publishRaw (handle : @&Handle) (payload : @&String) : IO Unit
@[extern "lc_queue_receive"]
private opaque receiveRaw (handle : @&Handle) : IO (Option (String × UInt64))
@[extern "lc_queue_ack"]
private opaque acknowledgeRaw (handle owner : @&Handle) (receipt : UInt64) : IO Bool

/-- Delivery tags are channel-local. Retaining the connection identity prevents
a receipt from an old worker connection acknowledging a newer delivery. -/
structure Receipt where
  owner : Handle
  tag : UInt64

def acquire (config : Config) (run : String) (create := false) (consume := true) : IO Handle := do
  unless 0 < config.port && config.port < 65536 do throw (IO.userError "Invalid RabbitMQ port")
  openRaw config.host config.port.toUInt32 config.vhost config.user config.password
    (config.queuePrefix ++ run) create consume

def Handle.enqueue (handle : Handle) (location : Location) : IO Unit :=
  publishRaw handle (toJson location).compress

def transport (handle : Handle) : LeaseQueue Unit IO Receipt where
  enqueue location state := return (← handle.enqueue location, state)
  dequeue state := do
    let some (payload, receipt) ← receiveRaw handle | return (none, state)
    let location ← match Json.parse payload >>= fromJson? (α := Location) with
      | .ok location => pure location
      | .error _ => throw (IO.userError "Invalid location in RabbitMQ delivery")
    IO.println s!"work {location.key}"
    (← IO.getStdout).flush
    return (some (location, ⟨handle, receipt⟩), state)
  acknowledge receipt state := return (← acknowledgeRaw handle receipt.owner receipt.tag, state)

def connect (config : Config) (run : String) : IO (Worker.Connection (LeaseQueue Unit IO Receipt)) := do
  let handle ← acquire config run
  return ⟨transport handle, handle.close⟩

end LeanCloudRuntime.RabbitMQ
