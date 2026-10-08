import LeanCloudRuntime.Program
import LeanCloudCli.IO
import LeanCloudCli.Model

namespace LeanCloudRuntime.Application
open Lean LeanCloud LeanEff LeanCloudCli

/-- Runtime services used by the application protocol. User code stays in the registry. -/
inductive Service : Type → Type where
  | submit (config : Config) (run entry : String) (input : Json) : Service Unit
  | health (config : Config) : Service Unit
  | configure (config : Config) (routes : Array HttpMailbox.WorkerEndpoint) : Service Unit
  | membership (config : Config) : Service LeanCloud.Pool.Membership
  | workerStopped (config : Config) (worker : String) (generation : Nat) : Service Unit
  | serveScheduler (config : Config) : Service Unit
  | serveWorker (config : Config) : Service Unit
  | control (config : Config) (run : String) (mode : LeanCloud.Pool.Mode) : Service Unit
  | scheduler (config : Config) (run : String) : Service Unit
  | worker (config : Config) (run : String) : Service Unit
  | definition (config : Config) (run : String) : Service RunDefinition
  | outcome (config : Config) (run : String) : Service (Option Exit)
  | cancel (config : Config) (run : String) : Service (Option Exit)
  | referenceStatus (config : Config) (run : String) : Service Scheduler.State
  | status (config : Config) (run : String) : Service Timing.Status
  | readText (config : Config) (ref : BlobRef) : Service String

inductive Runtime : Effect where
  | request (service : Service α) : Runtime (Except String α)

abbrev App := ExceptT String (Eff [Host, Runtime])

private def host (op : HostOp α) : App α := ExceptT.mk (send (Host.request op))
private def service (op : Service α) : App α := ExceptT.mk (send (Runtime.request op))
private def say (text : String) : App Unit := host (.write (text ++ "\n"))

/-- One protocol for every compiled application, independent of the actual services. -/
def run (registry : Registry) (args : List String) : App UInt32 := do
  try
    liftExcept registry.validate
    match args with
    | ["programs"] =>
      say (toJson (registry.programs.map (·.info))).compress
      pure 0
    | ["validate", entry] =>
      let program ← liftExcept (registry.find entry)
      let input ← liftExcept (Json.parse (← host .readLine))
      liftExcept (program.validate input)
      pure 0
    | [command, path] =>
      let config : Config ← liftExcept (Json.parse (← host (.readFile path)) >>= fromJson?)
      liftExcept config.mailboxes.validate
      unless config.scheduler.assignmentMs > 0 do throw "Assignment timeout must be positive"
      match command with
      | "pool-health" => service (.health config); pure 0
      | "pool-configure" =>
        let routes ← liftExcept (Json.parse (← host .readLine) >>= fromJson?)
        liftExcept ({ config.mailboxes with workers := routes }.validate)
        service (.configure config routes)
        pure 0
      | "pool-workers" => say (toJson (← service (.membership config))).compress; pure 0
      | "serve-scheduler" => service (.serveScheduler config); pure 0
      | "serve-worker" => service (.serveWorker config); pure 0
      | _ => throw "Expected serve-scheduler or serve-worker"
    | command :: path :: id :: rest =>
      unless LeanCloudCli.validId id do throw "Invalid run ID"
      let config : Config ← liftExcept (Json.parse (← host (.readFile path)) >>= fromJson?)
      liftExcept config.mailboxes.validate
      unless config.scheduler.assignmentMs > 0 do throw "Assignment timeout must be positive"
      match command, rest with
      | "pool-stopped", [generation] =>
        let some generation := generation.toNat? | throw "Expected membership generation"
        service (.workerStopped config id generation)
        pure 0
      | "submit-entry", [entry, file] =>
        let text ← if file == "-" then host .readLine else host (.readFile file)
        let input ← liftExcept (Json.parse text)
        let program ← liftExcept (registry.find entry)
        liftExcept (program.validate input)
        service (.submit config id entry input)
        say s!"submitted {id}"
        pure 0
      | "submit", files =>
        let some program := registry.programs[0]? | throw "Application has no programs"
        let input ← match files with
          | [] => match program.info.sampleInput with
            | some input => pure input
            | none => throw "This program needs an input file"
          | [file] => liftExcept (Json.parse (← host (.readFile file)))
          | _ => throw "Expected at most one input file"
        liftExcept (program.validate input)
        service (.submit config id program.info.entry input)
        say s!"submitted {id}"
        pure 0
      | "pause", [] => service (.control config id .paused); pure 0
      | "resume", [] => service (.control config id .active); pure 0
      | "scheduler", [] => service (.scheduler config id); pure 0
      | "worker", [] =>
        service (.worker config id)
        say s!"completed {id}"
        pure 0
      | "reference-status", [] => say (toJson (← service (.referenceStatus config id))).compress; pure 0
      | "status", [] => say (toJson (← service (.status config id))).compress; pure 0
      | "outcome", [] => say (toJson (← service (.outcome config id))).compress; pure 0
      | "cancel", [] => say (toJson (← service (.cancel config id))).compress; pure 0
      | "result", [] =>
        match ← service (.outcome config id) with
        | none => say "pending"; pure 2
        | some (.failure error) => throw error.message
        | some (.cancelled reason) => throw reason
        | some (.success value) =>
          let definition ← service (.definition config id)
          if definition.resultSchema == (inferInstance : Codec BlobRef).schema then
            let ref ← liftExcept (Codec.decode (α := BlobRef) value)
            host (.write (← service (.readText config ref)))
          else say value.pretty
          pure 0
      | _, _ => throw "Unknown application command or invalid arguments"
    | _ =>
      say "Usage: APP programs | validate ENTRY | (serve-scheduler|serve-worker|pool-health) CONFIG | (submit-entry|submit|pause|resume|status|outcome|result|cancel) CONFIG RUN [ARGS]"
      pure 2
  catch error => host (.write (error ++ "\n") true); pure 1

partial def runWith [Monad m]
    (handleHost : {α : Type} → HostOp α → m (Except String α))
    (handleService : {α : Type} → Service α → m (Except String α))
    (program : App α) : m (Except String α) := do
  match program.run with
  | .pure value => pure value
  | .impure (.here (.request operation)) next =>
    let value ← handleHost operation
    runWith handleHost handleService (ExceptT.mk (ArrsF.apply next value))
  | .impure (.there (.here (.request operation))) next =>
    let value ← handleService operation
    runWith handleHost handleService (ExceptT.mk (ArrsF.apply next value))
  | .impure (.there (.there rest)) _ => nomatch rest

private def handle (registry : Registry) (prepare : Config → String → Json → IO Unit) : Service α → IO α
  | .submit config id entry input => do
    S3.initializeBucket config.blobs
    prepare config entry input
    registry.submit config id entry input
    Pool.submit config id
  | .health config => discard (Pool.request config .health)
  | .configure config routes => discard (Pool.configure config routes)
  | .membership config => do IO.ofExcept (fromJson? (← Pool.request config .workers))
  | .workerStopped config worker generation => discard (Pool.request config (.workerStopped worker generation))
  | .serveScheduler config => Pool.scheduler config
  | .serveWorker config => registry.serveWorker config
  | .control config id mode => do
    discard (Pool.request config (match mode with
      | .active => .resume id | .paused => .pause id | .killed => .kill id))
  | .scheduler config id => runScheduler config id
  | .worker config id => registry.runWorker config id
  | .definition config id => loadRun config id
  | .outcome config id => completed config id
  | .cancel config id => do
    discard (Pool.request config (.kill id))
    completed config id
  | .referenceStatus config id => LeanCloudRuntime.status config id
  | .status config id => Pool.observation config id
  | .readText config ref => do
    let bytes ← match ← (S3.readBytes config.blobs ref).run with
      | .ok bytes => pure bytes
      | .error error => throw (IO.userError error.message)
    let some text := String.fromUTF8? bytes | throw (IO.userError "Result blob is not UTF-8 text")
    pure text

private def handleService (registry : Registry) (prepare : Config → String → Json → IO Unit)
    (op : Service α) : IO (Except String α) := do
  try return .ok (← handle registry prepare op)
  catch error => return .error error.toString

/-- HTTP exposes the same effect program as the executable, with a restricted
host interpreter: no filesystem paths or executable commands from the caller. -/
def api (registry : Registry) (config : Config) (prepare : Config → String → Json → IO Unit)
    (json : Json) : IO Json := do
  let args ← IO.ofExcept (json.getObjValAs? (Array String) "args")
  let input ← IO.ofExcept (json.getObjValAs? (Option String) "input")
  let allowed := match args.toList with
    | ["programs"] | ["validate", _] => true
    | [command, _] => ["pool-health", "pool-configure", "pool-workers"].contains command
    | [command, _, _] => ["pause", "resume", "status", "outcome", "result", "cancel"].contains command
    | ["pool-stopped", _, _, _] | ["submit-entry", _, _, _, "-"] => true
    | _ => false
  unless allowed do throw (IO.userError "Unsupported HTTP application command")
  let args := if args.size ≥ 2 && args[0]? != some "validate" then
    args.set! 1 "/etc/lean-cloud/config.json" else args
  let output ← IO.mkRef ({} : ProcessOutput)
  let host : {α : Type} → HostOp α → IO (Except String α) := fun {α} op =>
    match op with
    | .readFile path => do
      if path.toString == "/etc/lean-cloud/config.json" then return .ok (toJson config).compress
      else return .error "HTTP commands cannot read host files"
    | .readLine => pure (.ok (input.getD ""))
    | .write text stderr => do
      output.modify fun out => if stderr then { out with stderr := out.stderr ++ text }
        else { out with stdout := out.stdout ++ text }
      return .ok ()
    | _ => pure (.error "Unsupported HTTP host operation")
  let result ← runWith host (handleService registry prepare) (run registry args.toList)
  return toJson { (← output.get) with exitCode := result.toOption.getD 1 }

/-- Users only supply their registry. A node runs its HTTP API, embedded SQLite
inbox, and actor concurrently in this process; Docker restarts the whole node. -/
def main (registry : Registry) (args : List String)
    (prepare : Config → String → Json → IO Unit := fun _ _ _ => pure ()) : IO UInt32 := do
  let execute := withHostIO fun handleHost => do
    let result ← runWith handleHost (handleService registry prepare) (run registry args)
    return result.toOption.getD 1
  match args with
  | [command, path] =>
    if command == "serve-scheduler" || command == "serve-worker" || command == "serve-mailbox" then
      let config ← Config.load path
      let endpoint ← if command == "serve-worker" then IO.ofExcept (config.mailboxes.worker (← workerId))
        else pure config.mailboxes.scheduler
      let api := if command == "serve-scheduler" then api registry config prepare
        else fun _ => throw (IO.userError "Application commands belong to the scheduler")
      let database := (← IO.getEnv "CLOUD_INBOX_DATABASE").getD "/mailbox/inbox.sqlite"
      let actor := if command == "serve-mailbox" then do
          repeat IO.sleep 1000
          pure (0 : UInt32)
        else execute
      HttpMailbox.withServer endpoint database api actor (handleSignals := true)
    else execute
  | _ => execute

end LeanCloudRuntime.Application
