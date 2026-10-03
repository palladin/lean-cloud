import LeanCloud.Worker

namespace LeanCloudRuntime.RabbitMQ
open Lean LeanCloud

structure Config where
  host : String
  port : Nat := 5672
  vhost : String := "/"
  user : String
  password : String
  queuePrefix : String := "lean-cloud.mailbox."
  deriving FromJson, ToJson, Inhabited

/-- A stable worker identity and the independent broker hosting its inbox. -/
structure WorkerBroker where
  worker : WorkerId
  broker : Config
  deriving FromJson, ToJson, Inhabited

/-- Brokers are independent; sends connect directly to the recipient's broker. -/
structure Mailboxes where
  scheduler : Config
  workers : Array WorkerBroker
  deriving FromJson, ToJson

def Mailboxes.worker (config : Mailboxes) (id : WorkerId) : Except String Config := do
  let some node := config.workers.find? (·.worker == id)
    | throw s!"No mailbox broker configured for worker '{id}'"
  return node.broker

def Mailboxes.validate (config : Mailboxes) : Except String Unit := do
  let mut ids : Array String := #[]
  for node in config.workers do
    unless !node.worker.isEmpty && node.worker.length ≤ 64 && node.worker.toList.all (fun c =>
        c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_')) do
      throw "Worker ids must contain 1–64 ASCII letters, digits, '-' or '_'"
    if ids.contains node.worker then throw s!"Duplicate worker mailbox: {node.worker}"
    ids := ids.push node.worker
  for broker in #[config.scheduler] ++ config.workers.map (·.broker) do
    unless !broker.host.isEmpty && 0 < broker.port && broker.port ≤ 65535 do
      throw "Each RabbitMQ endpoint needs a host and a port between 1 and 65535"

private opaque HandleType : NonemptyType
def Handle := HandleType.type
instance : Nonempty Handle := HandleType.property

@[extern "lc_queue_open"]
private opaque openRaw (host : @&String) (port : UInt32) (vhost user password queue : @&String)
  (create consume : Bool) : IO Handle
@[extern "lc_queue_close"] opaque Handle.close (handle : @&Handle) : IO Unit
@[extern "lc_queue_publish"] private opaque publishRaw (handle : @&Handle) (payload : @&String) : IO Unit
@[extern "lc_queue_receive"] private opaque receiveRaw (handle : @&Handle) : IO (Option (String × UInt64))
@[extern "lc_queue_ack"] private opaque acknowledgeRaw (handle owner : @&Handle) (receipt : UInt64) : IO Bool
@[extern "lc_queue_delete"] opaque Handle.delete (handle : @&Handle) : IO Unit

/-- Each named actor has its own durable classic queue on its configured broker.
No TTL, auto-delete, or delivery limit may discard a required delivery.
Single-active-consumer mode delivers to one consumer at a time. -/
def openMailbox (config : Config) (run actor : String) (consume := true) : IO Handle := do
  unless 0 < config.port && config.port < 65536 do throw (IO.userError "Invalid RabbitMQ port")
  openRaw config.host config.port.toUInt32 config.vhost config.user config.password
    (config.queuePrefix ++ run ++ "." ++ actor) true consume

def Handle.send [ToJson α] (handle : Handle) (message : α) : IO Unit :=
  publishRaw handle (toJson message).compress

def inbox [FromJson α] (handle : Handle) : Mailbox IO α where
  receive := do
    let some (payload, tag) ← receiveRaw handle | return none
    let message ← IO.ofExcept (Json.parse payload >>= fromJson?)
    return some ⟨tag.toNat, message⟩
  acknowledge receipt := do
    unless ← acknowledgeRaw handle handle receipt.toUInt64 do
      throw (IO.userError "Receipt does not belong to the current mailbox delivery")

/-- The destination queue is declared durably before publishing. Confirmation is
required even when the destination actor is currently stopped. -/
def send [ToJson α] (config : Config) (run actor : String) (message : α) : IO Unit := do
  let handle ← openMailbox config run actor false
  try handle.send message finally handle.close

/-- Temporary status replies stay on the scheduler's broker; workflow replies
go to the worker's configured broker. Unknown worker identities never fall back
to a shared broker. -/
def Mailboxes.sendWorker (config : Mailboxes) (run : String) (delivery : Delivery) : IO Unit := do
  let broker ← match delivery.message with
    | .status _ => pure config.scheduler
    | _ => IO.ofExcept (config.worker delivery.worker)
  send broker run ("worker." ++ delivery.worker) delivery.message

end LeanCloudRuntime.RabbitMQ
