import LeanCloudRuntime.Program
import LeanCloudRuntime.Monitoring
import LeanCloudCli.IO
import LeanCloudCli.Model

namespace LeanCloudRuntime.Application
open Lean LeanCloud LeanEff LeanCloudCli

/-- Text output of the node's restricted administrative command endpoint. -/
structure CommandOutput where
  exitCode : UInt32 := 0
  stdout : String := ""
  stderr : String := ""

instance : ToJson CommandOutput where
  toJson out := Json.mkObj [("exitCode", toJson out.exitCode.toNat),
    ("stdout", toJson out.stdout), ("stderr", toJson out.stderr)]

instance : FromJson CommandOutput where
  fromJson? json := do
    let code ← json.getObjValAs? Nat "exitCode"
    unless code ≤ 4294967295 do throw "Invalid exit code"
    return ⟨code.toUInt32, ← json.getObjValAs? String "stdout", ← json.getObjValAs? String "stderr"⟩

/-- Runtime services used by the application protocol. User code stays in the registry. -/
inductive Service : Type → Type where
  | submit (config : Config) (run entry : String) (input : Json) : Service Unit
  | health (config : Config) : Service Unit
  | configure (config : Config) (routes : Array HttpMailbox.WorkerEndpoint) : Service Unit
  | membership (config : Config) : Service LeanCloud.Pool.Membership
  | runs (config : Config) (after : Option String) (limit : Nat) : Service (Array (String × LeanCloud.Pool.Mode))
  | mode (config : Config) (run : String) : Service LeanCloud.Pool.Mode
  | durableControl (config : Config) (requestId : String) (command : LeanCloud.Pool.Command) : Service (Except String Unit)
  | workerStopped (config : Config) (worker : String) (generation : Nat) : Service Unit
  | serveScheduler (config : Config) : Service Unit
  | serveWorker (config : Config) : Service Unit
  | control (config : Config) (run : String) (mode : LeanCloud.Pool.Mode) : Service Unit
  | definition (config : Config) (run : String) : Service RunDefinition
  | outcome (config : Config) (run : String) : Service (Option Exit)
  | cancel (config : Config) (run : String) : Service (Option Exit)
  | status (config : Config) (run : String) : Service Timing.Status
  | readText (config : Config) (ref : BlobRef) : Service String
  | remove (config : Config) (run : String) : Service Unit
  | purge (config : Config) (run : String) : Service Unit
  | nodes (config : Config) : Service (Array DeploymentApi.Node)
  | observations (config : Config) (run worker : String) (after : Option String) (limit : Nat) : Service DeploymentApi.ObservationPage

inductive Runtime : Effect where
  | request (service : Service α) : Runtime (Except String α)

abbrev App := ExceptT String (Eff [Host, Runtime])

private def host (op : HostOp α) : App α := ExceptT.mk (send (Host.request op))
private def service (op : Service α) : App α := ExceptT.mk (send (Runtime.request op))
private def say (text : String) : App Unit := host (.write (text ++ "\n"))

private def runInfo (config : Config) (id : String) (mode : LeanCloud.Pool.Mode) : App DeploymentApi.RunInfo := do
  let definition ← service (.definition config id)
  return { id, entry := definition.entry, input := definition.input, resultSchema := definition.resultSchema, mode
           image := definition.image, program := definition.program }

/-- The public API shares the application's service effects and typed registry.
It cannot invoke the private mailbox/host administration protocol. -/
private def deploymentRequest (registry : Registry) (config : Config) (client : ClientConfig) :
    (request : DeploymentApi.Request) → App (DeploymentApi.Response request)
  | .describe => pure { deployment := client.deployment, image := client.image }
  | .programs => pure (registry.programs.map (·.info))
  | .nodes => service (.nodes config)
  | .observations run worker after limit => service (.observations config run worker after limit)
  | .runs after limit => do
    let entries ← service (.runs config after limit)
    let items ← entries.mapM fun (id, mode) => do
      let info ← runInfo config id mode
      -- Source is fetched for one selected run. Catalog pages stay small even
      -- when an application bundles a large source tree.
      return { info with program := info.program.map fun program => { program with sources := #[] } }
    return { items, next := if items.size == limit then items.back?.map (·.id) else none }
  | .run id => do runInfo config id (← service (.mode config id))
  | .submit id entry input => do
    let program ← liftExcept (registry.find entry)
    liftExcept (program.validate input)
    service (.submit config id program.info.entry input)
  | .control requestId id action => do
    if action == .resume then
      let definition ← service (.definition config id)
      unless definition.image.all (· == client.image) do throw "This run belongs to a different application image"
    service (.durableControl config requestId (action.command id))
  | .remove requestId id => do
    let receipt ← service (.durableControl config requestId (.remove id))
    if let .error error := receipt then return .error error
    -- Cleanup is idempotent and must be retried even when retirement was
    -- already committed by a request whose HTTP response was lost.
    service (.remove config id)
    return .ok ()
  | .inspect id => service (.status config id)
  | .outcome id => service (.outcome config id)
  | .result id => do
    let some outcome ← service (.outcome config id) | throw "Workflow result is pending"
    match outcome with
    | .failure error => throw error.message
    | .cancelled reason => throw reason
    | .success value =>
      let definition ← service (.definition config id)
      if definition.resultSchema == (inferInstance : Codec BlobRef).schema then
        service (.readText config (← liftExcept (Codec.decode value)))
      else return value.pretty

def deploymentRun (registry : Registry) (config : Config) (client : ClientConfig)
    (request : DeploymentApi.Request) : App (DeploymentApi.Response request) := do
  liftExcept request.validate
  liftExcept registry.validate
  deploymentRequest registry config client request

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
      liftExcept config.validate
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
      liftExcept config.validate
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
      | "status", [] => say (toJson (← service (.status config id))).compress; pure 0
      | "outcome", [] => say (toJson (← service (.outcome config id))).compress; pure 0
      | "cancel", [] => say (toJson (← service (.cancel config id))).compress; pure 0
      | "remove", [] => service (.remove config id); pure 0
      | "purge-run", [] => service (.purge config id); pure 0
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

/-- Visit every active node even if one fails. Retirement is already durable;
retrying removal repeats safe cleanup instead of reporting partial work as success. -/
def cleanupWorkers (routes : Array HttpMailbox.WorkerEndpoint)
    (purge : HttpMailbox.WorkerEndpoint → IO Unit) : IO Unit := do
  if routes.isEmpty then
    throw (IO.userError "Run retired; cleanup incomplete. Add a worker, then retry removal.")
  let mut failures := #[]
  for route in routes do
    try purge route
    catch error => failures := failures.push s!"{route.worker}: {error}"
  unless failures.isEmpty do
    throw (IO.userError ("Run retired; cleanup incomplete. Retry removal. " ++ String.intercalate "; " failures.toList))

private def handle (registry : Registry) (prepare : Config → String → Json → IO Unit)
    (observations : Option ObservationStore.Store) (replayCache : Option ReplayCache.Cache) : Service α → IO α
  | .submit config id entry input => do
    let removed : Bool ← IO.ofExcept (fromJson? (← Pool.request config (.removed id)))
    if removed then throw (IO.userError "Run was removed; use a new run ID")
    config.objects.ensureContainer
    prepare config entry input
    registry.submit config id entry input
    Pool.submit config id
  | .health config => discard (Pool.request config .health)
  | .configure config routes => discard (Pool.configure config routes)
  | .membership config => do IO.ofExcept (fromJson? (← Pool.request config .workers))
  | .runs config after limit => do IO.ofExcept (fromJson? (← Pool.request config (.runs after limit)))
  | .mode config id => do IO.ofExcept (fromJson? (← Pool.request config (.mode id)))
  | .durableControl config requestId command => Pool.control config requestId command
  | .workerStopped config worker generation => discard (Pool.request config (.workerStopped worker generation))
  | .serveScheduler config => Pool.scheduler (config.localInbox none)
      (observations.map (·.record) |>.getD (fun _ => pure ()))
      (observations.map (·.remove) |>.getD (fun _ => pure ()))
  | .serveWorker config => do
    -- A retained node can return after scaling down or being offline during
    -- removal. Rehydrate retirement before accepting old inbox deliveries.
    let retired : Array String ← IO.ofExcept (fromJson? (← Pool.request config .removedRuns))
    for run in retired do
      if let some store := observations then store.remove run
      if let some cache := replayCache then cache.remove run
    registry.serveWorker (config.localInbox (some (← workerId)))
      (observations.map (·.record) |>.getD (fun _ => pure ())) replayCache
  | .nodes config => do
    let some store := observations | throw (IO.userError "Node telemetry is not configured")
    Monitoring.nodes config store
  | .observations config run worker after limit => do
    let some store := observations | throw (IO.userError "Node telemetry is not configured")
    Monitoring.observations config store run worker after limit
  | .control config id mode => do
    discard (Pool.request config (match mode with
      | .active => .resume id | .paused => .pause id | .killed => .kill id))
  | .definition config id => loadRun config id
  | .outcome config id => completed config id
  | .cancel config id => do
    discard (Pool.request config (.kill id))
    completed config id
  | .status config id => Pool.observation config id
  | .purge config id => do
    let removed : Bool ← IO.ofExcept (fromJson? (← Pool.request config (.removed id)))
    unless removed do throw (IO.userError "Run has not been retired; refusing to delete records")
    if let some store := observations then store.remove id
    if let some cache := replayCache then cache.remove id
    HttpMailbox.retireWorkQueues config.mailboxes.scheduler id
    config.objects.removeRun id
  | .remove config id => do
    discard <| Pool.request config (.remove id)
    if let some store := observations then store.remove id
    let membership ← Pool.request config .workers
    let routes : Array HttpMailbox.WorkerEndpoint ← IO.ofExcept (membership.getObjValAs? _ "routes")
    cleanupWorkers routes fun route => do
      let body := Json.mkObj [("args", toJson #["purge-run", "config", id]), ("input", Json.null)]
      let response ← LeanCloudCli.Http.post s!"http://{route.endpoint.host}:{route.endpoint.port}/app"
        route.endpoint.token body.compress
      let result : Except String Json ← IO.ofExcept (Json.parse response >>= fromJson?)
      let output : CommandOutput ← IO.ofExcept (result >>= fromJson?)
      unless output.exitCode == 0 do throw (IO.userError (output.stderr ++ output.stdout))
  | .readText config ref => do
    let bytes ← match ← (config.objects.readBytes ref).run with
      | .ok bytes => pure bytes
      | .error error => throw (IO.userError error.message)
    let some text := String.fromUTF8? bytes | throw (IO.userError "Result blob is not UTF-8 text")
    pure text

private def handleService (registry : Registry) (prepare : Config → String → Json → IO Unit)
    (observations : Option ObservationStore.Store := none)
    (replayCache : Option ReplayCache.Cache := none)
    (op : Service α) : IO (Except String α) := do
  try return .ok (← handle registry prepare observations replayCache op)
  catch error => return .error error.toString

def deploymentApi (registry : Registry) (config : Config) (client : ClientConfig)
    (prepare : Config → String → Json → IO Unit) (json : Json)
    (observations : Option ObservationStore.Store := none) : IO Json := do
  let request ← IO.ofExcept (DeploymentApi.Request.decode json)
  match request with
  | .describe => pure ()
  | _ =>
    unless (json.getObjValAs? String "deployment").toOption == some client.deployment do
      throw (IO.userError "Deployment identity mismatch; reconnect before sending commands")
  let result ← runWith (fun _ => pure (.error "Deployment API cannot access the CLI host"))
    (handleService registry prepare observations none) (deploymentRun registry config client request)
  return toJson (← IO.ofExcept result)

/-- HTTP exposes the same effect program as the executable, with a restricted
host interpreter: no filesystem paths or executable commands from the caller. -/
def api (registry : Registry) (config : Config) (prepare : Config → String → Json → IO Unit)
    (json : Json) (worker := false) (observations : Option ObservationStore.Store := none)
    (replayCache : Option ReplayCache.Cache := none) : IO Json := do
  let args ← IO.ofExcept (json.getObjValAs? (Array String) "args")
  let input ← IO.ofExcept (json.getObjValAs? (Option String) "input")
  let allowed := if worker then args.toList matches ["purge-run", _, _] else match args.toList with
    | ["programs"] | ["validate", _] => true
    | [command, _] => ["pool-health", "pool-configure", "pool-workers"].contains command
    | [command, _, _] => ["pause", "resume", "status", "outcome", "result", "cancel", "remove"].contains command
    | ["pool-stopped", _, _, _] | ["submit-entry", _, _, _, "-"] => true
    | _ => false
  unless allowed do throw (IO.userError "Unsupported HTTP application command")
  let args := if args.size ≥ 2 && args[0]? != some "validate" then
    args.set! 1 "/etc/lean-cloud/config.json" else args
  let output ← IO.mkRef ({} : CommandOutput)
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
  let result ← runWith host (handleService registry prepare observations replayCache) (run registry args.toList)
  return toJson { (← output.get) with exitCode := result.toOption.getD 1 }

/-- Users only supply their registry. A node runs its HTTP API, embedded SQLite
inbox, and actor concurrently in this process; Docker restarts the whole node. -/
def main (registry : Registry) (args : List String)
    (prepare : Config → String → Json → IO Unit := fun _ _ _ => pure ()) : IO UInt32 := do
  let execute (observations : Option ObservationStore.Store := none)
      (replayCache : Option ReplayCache.Cache := none) := withHostIO fun handleHost => do
    let result ← runWith handleHost (handleService registry prepare observations replayCache) (run registry args)
    return result.toOption.getD 1
  match args with
  | [command, path] =>
    if command == "serve-scheduler" || command == "serve-worker" then
      let config ← Config.load path
      let endpoint ← if command == "serve-worker" then IO.ofExcept (config.mailboxes.worker (← workerId))
        else pure config.mailboxes.scheduler
      let database := (← IO.getEnv "CLOUD_INBOX_DATABASE").getD "/mailbox/inbox.sqlite"
      let worker ← if command == "serve-worker" then workerId else pure "scheduler"
      let cache ← ReplayCache.create config.worker.replayCacheBytes config.worker.replayCacheEntries
      ObservationStore.withStore (database ++ ".telemetry.sqlite") worker fun store => do
        let api := fun json => api registry config prepare json (worker := command == "serve-worker")
          (observations := some store) (replayCache := some cache)
        let client := if command == "serve-scheduler" then config.client.map fun client =>
          { token := client.token, api := fun json => deploymentApi registry config client prepare json (some store) : HttpMailbox.ClientHandler }
          else none
        HttpMailbox.withServer endpoint database api (HttpServer.runNode (execute (some store) (some cache)))
          (handleSignals := true) (client := client)
          (telemetry := some (Monitoring.api store))
    else execute none
  | _ => execute none

end LeanCloudRuntime.Application
