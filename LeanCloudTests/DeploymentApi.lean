import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel
import LeanCloud.ControlReceipts

namespace LeanCloudTests.DeploymentApi
open Lean LeanCloud LeanCloudCli

private def pauseResume : IO Unit := do
  let state : Pool.State := { runs := #[{ id := "one" }] }
  let (paused, receipts, first) := ControlReceipts.apply state #[] "pause-1" (.pause "one")
  assertTrue first.isOk "Pause failed"
  let (active, receipts, resumed) := ControlReceipts.apply paused receipts "resume-1" (.resume "one")
  assertTrue resumed.isOk "Resume failed"
  -- Simulate catalog/receipt persistence and process reconstruction. Retrying an
  -- old pause must not undo the more recent resume, even with a fresh reply inbox.
  let catalog : Pool.Catalog ← unwrap (fromJson? (toJson active.catalog))
  let receipts : Array ControlReceipts.Receipt ← unwrap (fromJson? (toJson receipts))
  let (retried, after, replayed) := ControlReceipts.apply catalog.restore receipts "pause-1" (.pause "one")
  assertEq (toJson replayed) (toJson first)
  assertEq (retried.runs[0]?.map (·.mode)) (some .active) "Delayed retry reapplied stale pause"
  assertEq after.size receipts.size "Retry allocated another receipt"
  let (conflict, after, result) := ControlReceipts.apply retried receipts "pause-1" (.kill "one")
  assertTrue (!result.isOk) "Reused ID accepted another command"
  assertEq (conflict.runs[0]?.map (·.mode)) (some .active)
  assertEq after.size receipts.size

private structure ClientWorld where
  requests : Array (String × Json) := #[]
  secret : String := "client-secret"

private def clientHost : HostOp α → StateM ClientWorld (Except String α)
  | .getEnv "CLOUD_TOKEN" => return .ok (some (← get).secret)
  | .readFile path =>
    if path == "/client.token" then return .ok ((← get).secret ++ "\n")
    else return .error "Missing credential file"
  | .httpPost url token text => do
    let action : ExceptT String (StateM ClientWorld) Json := do
      unless token == (← get).secret do throw "Wrong credential"
      let body ← liftExcept (Json.parse text)
      let operation ← liftExcept (LeanCloud.DeploymentApi.Request.decode body)
      modify fun world => { world with requests := world.requests.push (url, body) }
      match operation with
      | .describe => return toJson ({ deployment := "production", image := "sha256:app" } : LeanCloud.DeploymentApi.Info)
      | .control _ _ _ =>
        unless (body.getObjValAs? String "deployment").toOption == some "production" do throw "Identity mismatch"
        return toJson (.ok () : Except String Unit)
      | _ => throw "Unexpected API operation"
    let (result, world) := action.run.run (← get)
    set world
    return .ok (toJson (result : Except String Json)).compress
  | _ => pure (.error "Remote API touched a filesystem, terminal, or process")

private def remoteHost (url token : String) (json : Json) : Except String Json := do
  unless url == "https://cloud.example.test/deployment" && token == "secret" do throw "Wrong endpoint/credential"
  let operation ← LeanCloud.DeploymentApi.Request.decode json
  if let .describe := operation then pure ()
  else unless (json.getObjValAs? String "deployment").toOption == some "production" do throw "Wrong deployment"
  let value ← match operation with
    | .describe => pure (toJson ({ deployment := "production", image := "sha256:app" } : LeanCloud.DeploymentApi.Info))
    | .programs => pure (toJson (#[{
        entry := "squares/v1", inputSchema := "array/nat", resultSchema := "nat"
        description := "Squares", sampleInput := some (toJson #[1, 2, 3]) }] : Array ProgramInfo))
    | .runs _ _ => pure (toJson ({ items := #[] } : LeanCloud.DeploymentApi.Page LeanCloud.DeploymentApi.RunInfo))
    | .nodes => pure (toJson (#[{ id := "scheduler", online := true }] : Array LeanCloud.DeploymentApi.Node))
    | .submit _ _ _ => pure (toJson ())
    | .control _ _ _ | .remove _ _ => pure (toJson (.ok () : Except String Unit))
    | _ => throw "Unexpected operation"
  return toJson (.ok value : Except String Json)

private def remoteWorld : ConsoleModel.World := {
  envs := #[("LEAN_CLOUD_TOKEN", "secret")], http := some remoteHost }

private def remoteContext : Context := ⟨"/connections", "production"⟩

private def withConnection (world : ConsoleModel.World := remoteWorld) : ConsoleModel.World :=
  world.json (remoteContext.home / "connection.json")
    ({ url := "https://cloud.example.test", deployment := "production", tokenEnv := "LEAN_CLOUD_TOKEN" } : Client.Connection)

private def monitoringHost (completed : Bool) (url token : String) (json : Json) : Except String Json := do
  let request ← LeanCloud.DeploymentApi.Request.decode json
  let value ← match request with
    | .nodes => pure (toJson (#[
        { id := "scheduler", online := true },
        { id := "worker1", online := true, samples := #[
          { incarnation := "boot", timeNs := 1000000000, cpuNs := some 0, memory := some 9437184, memoryLimit := some 16777216 },
          { incarnation := "boot", timeNs := 2000000000, cpuNs := some 500000000, memory := some 9437184, memoryLimit := some 16777216 }] },
        { id := "worker2", online := false, warning := "Node endpoint unavailable" }] : Array LeanCloud.DeploymentApi.Node))
    | .run id => pure (toJson ({
        id, entry := "squares/v1", input := Json.null, resultSchema := "nat", mode := .active
        program := some {
          entry := "squares/v1", inputSchema := "unit", resultSchema := "nat", description := "", sampleInput := none
          sources := #[⟨"Remote.lean", "cloud {\n  Cloud.pure work\n}", #[{ id := "work", line := 2, endLine := 2 }]⟩] }
        } : LeanCloud.DeploymentApi.RunInfo))
    | .outcome _ => pure (toJson (if completed then some (.success (toJson (55 : Nat))) else none : Option Exit))
    | .inspect _ => pure (toJson ({ jobs := #[⟨Location.root, Location.root, false,
        if completed then .done else .running "worker1" 0 1000⟩] } : Timing.Status))
    | .observations run worker _ _ =>
      let step : Observations.Step := {
        timestamp := "1", event := ⟨"boot", 1, 1, worker, some 0, "0:0", "execute", "work", run, some "work"⟩
        branch := some Location.root
        resources := if worker == "scheduler" then none else some {
          incarnation := "boot", timeNs := 1000000000, memory := some 1048576, memoryLimit := some 16777216 }
        job := if worker == "scheduler" then some {
          branch := Location.root, location := Location.root, joining := false
          status := if completed then .done else .running "worker1" 0 } else none }
      pure (toJson ({ items := #[step] } : LeanCloud.DeploymentApi.ObservationPage))
    | _ => return ← remoteHost url token json
  return toJson (.ok value : Except String Json)

def cases : Array TestCase := #[
  ⟨"deployment-api.watch-bounded-refresh-pages", do
    let http url token json := do
      match ← LeanCloud.DeploymentApi.Request.decode json with
      | .observations run worker after _ =>
        let second := after == some "page-one"
        let step : Observations.Step := {
          timestamp := if second then "2" else "1"
          event := ⟨"boot", if second then 2 else 1, 0, worker, none, "0:0", "execute", "", run, none⟩ }
        let page : LeanCloud.DeploymentApi.ObservationPage := {
          items := #[step], next := if second then none else some "page-one" }
        return toJson (.ok (toJson page) : Except String Json)
      | _ => monitoringHost false url token json
    let initial := withConnection { remoteWorld with http := some http }
    let action : Cli Unit := do
      let run ← remoteContext.loadRun "one"
      let first ← Trace.load remoteContext run (some #[])
      unless first.cursors.all (·.2 == some "page-one") do throw "First refresh drained all pages"
      let second ← Trace.load remoteContext run (some first.cursors)
      unless second.cursors.all (·.2.isNone) do throw "Cursor did not wrap for updated slots"
      unless second.steps.any (·.event.seq == 2) do throw "Next refresh did not advance"
    let (result, world) := ConsoleModel.run action initial
    discard <| unwrap result
    let pages := world.httpRequests.filter fun json =>
      match (LeanCloud.DeploymentApi.Request.decode json).toOption with
      | some (.observations ..) => true | _ => false
    assertEq pages.size 4 "Refresh made more than one request per online node"⟩,
  ⟨"deployment-api.watch-keyboard-during-slow-http", do
    let initial := withConnection { remoteWorld with http := some (monitoringHost false) }
    let (result, saved) := ConsoleModel.run (command remoteContext ["watch", "one", "--once"]) initial
    discard <| unwrap result
    let initial := { saved with
      stdout := "", trace := #[], httpDelay := 10000
      keys := [27, 91, 66, 113] } -- Down, then q while the server is still pending.
    let (result, world) := ConsoleModel.run (command remoteContext ["watch", "one"]) initial
    discard <| unwrap result
    assertTrue world.keys.isEmpty "Watch did not read navigation/quit during HTTP"
    assertTrue (world.time - initial.time < 1000) "Quit waited for a slow refresh"
    assertTrue (world.trace.contains "httpStart" && world.trace.contains "httpCancel") "Request was not cancelled"
    assertTrue (world.pendingHttp.isEmpty && !world.terminal && world.locks.isEmpty) "Watch leaked host resources"
    assertTrue ((world.stdout.splitOn "Remote.lean:2").length > 1) "Watch hid its saved view during refresh"⟩,
  ⟨"deployment-api.background-fetch-result-and-errors", do
    for fails in [false, true] do
      let initial : ConsoleModel.World := {
        httpDelay := 500
        http := some fun _ _ _ => if fails then .error "offline" else .ok (toJson (42 : Nat)) }
      let program : Cli String := try request (.httpPost "https://example.test" "secret" "{}")
        catch error => pure error
      let (result, world) := ConsoleModel.run (Fetch.run program (fun n => do
        discard <| request (.key 100)
        return some (n + 1)) (0 : Nat)) initial
      let some (value, ticks) ← unwrap result | throw (IO.userError "Refresh unexpectedly abandoned")
      assertEq value (if fails then "offline" else "42")
      assertEq ticks 5
      assertTrue world.pendingHttp.isEmpty "Completed request retained a task"⟩,
  ⟨"deployment-api.remote-watch-and-top-no-local-processes", do
    for completed in [false, true] do
      let initial := withConnection { remoteWorld with http := some (monitoringHost completed) }
      let (result, world) := ConsoleModel.run (command remoteContext ["watch", "one", "--once"]) initial
      discard <| unwrap result
      for text in ["Remote.lean:2", "Cloud.pure work", "worker2 unavailable"] do
        assertTrue ((world.stdout.splitOn text).length > 1) s!"Missing remote watch field: {text}"
      let memory := if completed then "1.0 MiB" else "9.0 MiB"
      assertTrue ((world.stdout.splitOn memory).length > 1) "Watch used the wrong metric source"
      if completed then
        assertTrue ((world.stdout.splitOn "9.0 MiB").length == 1) "Final view used current counters"
      let (result, view) := ConsoleModel.run (command remoteContext ["top", "--once"]) initial
      discard <| unwrap result
      for text in ["worker1", "worker2", "50.00%", "9.0 MiB", "unavailable"] do
        assertTrue ((view.stdout.splitOn text).length > 1) s!"Missing remote top field: {text}"⟩,
  ⟨"deployment-api.remote-watch-retains-last-observations", do
    for completed in [false, true] do
      let initial := withConnection { remoteWorld with http := some (monitoringHost completed) }
      let (result, world) := ConsoleModel.run (command remoteContext ["watch", "one", "--once"]) initial
      discard <| unwrap result
      let unavailable url token json := do
        match ← LeanCloud.DeploymentApi.Request.decode json with
        | .nodes => throw "Endpoint temporarily unavailable"
        | _ => monitoringHost completed url token json
      let (result, world) := ConsoleModel.run (command remoteContext ["watch", "one", "--once"])
        { world with http := some unavailable, stdout := "" }
      discard <| unwrap result
      assertTrue ((world.stdout.splitOn "Remote.lean:2").length > 1) "Lost last view on telemetry failure"
      assertTrue ((world.stdout.splitOn "telemetry unavailable").length > 1) "Missing warning for stale observations"
      let (result, world) := ConsoleModel.run (command remoteContext ["watch", "one", "--once"])
        { world with http := some (fun _ _ _ => .error "Connection lost"), stdout := "" }
      discard <| unwrap result
      let savedStatus := if completed then "completed (saved)" else "result pending (saved)"
      for text in [savedStatus, "Remote.lean:2", "showing the saved workflow view"] do
        assertTrue ((world.stdout.splitOn text).length > 1) s!"Missing offline field: {text}"⟩,
  ⟨"deployment-api.remote-console-without-docker-or-checkout", do
    let action := do
      let (ctx, _) ← dispatch ⟨"/work", "local"⟩ ["connect", "production", "https://cloud.example.test"]
      discard <| command ctx ["programs"]
      discard <| command ctx ["run", "squares", "--input", "numbers.json", "--id", "example"]
      discard <| command ctx ["ps"]
      discard <| command ctx ["status"]
      discard <| command ctx ["doctor"]
      discard <| command ctx ["pause", "example"]
      discard <| command ctx ["resume", "example"]
      discard <| command ctx ["kill", "example"]
      discard <| command ctx ["remove", "example"]
      return ctx
    let (result, world) := ConsoleModel.run action (remoteWorld.save "/work/numbers.json" "[4,5]")
    let ctx ← unwrap result
    assertTrue world.locks.isEmpty "Remote control leaked a lock"
    assertTrue ((world.file (ctx.home / "connection.json")).isSome) "Connection not saved"
    let requests ← unwrap (world.httpRequests.mapM LeanCloud.DeploymentApi.Request.decode)
    assertTrue (requests.any fun request => match request with
      | .submit "example" "squares/v1" input => input == toJson #[4, 5]
      | _ => false) "Run did not use client input file"
    assertTrue ((world.stdout.splitOn "Squares").length > 1) "Server program catalog not displayed"
    let (result, cached) := ConsoleModel.run (Completion.load ctx) { world with http := some (fun _ _ _ => .error "Must not poll") }
    let catalog ← unwrap result
    assertEq catalog.programs.size 1
    assertEq cached.httpRequests.size world.httpRequests.size "Completion polled the deployment"⟩,
  ⟨"deployment-api.ambiguous-control-reuses-durable-id", do
    let world := withConnection { remoteWorld with http := some (fun _ _ _ => .error "Response lost") }
    let action := command remoteContext ["pause", "one"]
    let (failed, world) := ConsoleModel.run action world
    assertTrue (!failed.isOk) "Transport error swallowed"
    let path := remoteContext.directory "one" / "pending-control.json"
    assertTrue (world.file path).isSome "Ambiguous request identity lost"
    assertTrue world.locks.isEmpty "Failure leaked lock"
    let (conflict, unchanged) := ConsoleModel.run (command remoteContext ["kill", "one"]) world
    assertTrue (!conflict.isOk) "Conflicting uncertain request accepted"
    assertEq unchanged.httpRequests.size world.httpRequests.size "Conflict reached server"
    let (retried, world) := ConsoleModel.run action { world with http := some remoteHost }
    discard <| unwrap retried
    assertEq world.httpRequests[0]? world.httpRequests[1]? "Retry allocated another request identity"
    assertTrue (world.file path).isNone "Successful receipt not retired"
    assertEq world.nextId 1
    let (next, world) := ConsoleModel.run action world
    discard <| unwrap next
    assertEq world.nextId 2 "New user command reused an old receipt"⟩,
  ⟨"deployment-api.scheduler-timeout-retains-pending-request", do
    let world := withConnection { remoteWorld with http := some (fun _ _ _ =>
      .ok (toJson (.error "Scheduler timed out after committing" : Except String Json))) }
    let (result, world) := ConsoleModel.run (command remoteContext ["pause", "one"]) world
    assertTrue (!result.isOk) "Service timeout swallowed"
    assertTrue (world.file (remoteContext.directory "one" / "pending-control.json")).isSome
      "API transport uncertainty discarded request identity"⟩,
  ⟨"deployment-api.definitive-control-error-retires-pending-request", do
    let world := withConnection { remoteWorld with http := some (fun _ _ _ =>
      .ok (toJson (.ok (toJson (.error "Already completed" : Except String Unit)) : Except String Json))) }
    let (result, world) := ConsoleModel.run (command remoteContext ["pause", "one"]) world
    assertTrue (!result.isOk) "Server error swallowed"
    assertTrue (world.file (remoteContext.directory "one" / "pending-control.json")).isNone "Definite failure remained uncertain"
    assertTrue world.locks.isEmpty "Failure leaked lock"⟩,
  ⟨"deployment-api.remote-connection-never-falls-back-to-docker", do
    for args in [["deploy"], ["scale", "3"], ["up"], ["down"], ["clean"], ["backup", "/backup"],
        ["restore", "/backup"], ["cluster", "plan", "config.json"]] do
      let (result, world) := ConsoleModel.run (dispatch remoteContext args) (withConnection)
      assertTrue (!result.isOk) s!"Unsupported remote command accepted: {args}"
      assertTrue world.httpRequests.isEmpty "Unsupported command reached server"
      assertTrue world.locks.isEmpty "Unsupported command acquired lock"⟩,
  ⟨"deployment-api.durable-controls-survive-restart", pauseResume⟩,
  ⟨"deployment-api.failed-receipt-remains-failed", do
    let (state, receipts, failed) := ControlReceipts.apply {} #[] "pause" (.pause "later")
    assertTrue (!failed.isOk) "Missing run accepted"
    let (state, _) ← unwrap (Pool.command state (.submit "later"))
    let (state, _, result) := ControlReceipts.apply state receipts "pause" (.pause "later")
    assertEq (toJson result) (toJson failed)
    assertEq (state.runs[0]?.map (·.mode)) (some .active)
    let (_, receipts, result) := ControlReceipts.apply state receipts "read" (.status "later")
    assertTrue (!result.isOk) "Read operation allocated control receipt"
    assertEq receipts.size 1⟩,
  ⟨"deployment-api.version-and-request-validation", do
    let request : LeanCloud.DeploymentApi.Request := .control "request-1" "run-1" .pause
    let decoded ← unwrap (LeanCloud.DeploymentApi.Request.decode request.encode)
    assertEq (toJson decoded) (toJson request)
    for bad in [request.encode.setObjVal! "apiVersion" (toJson (999 : Nat)),
        toJson request, (.runs none 0 : LeanCloud.DeploymentApi.Request).encode,
        (.runs none 101 : LeanCloud.DeploymentApi.Request).encode,
        (.control "../bad" "run-1" .kill : LeanCloud.DeploymentApi.Request).encode,
        Json.mkObj [("apiVersion", toJson (1 : Nat)), ("request", Json.mkObj [("workerStopped", Json.null)])]] do
      assertTrue (!(LeanCloud.DeploymentApi.Request.decode bad).isOk) "Invalid public request accepted"⟩,
  ⟨"deployment-api.catalog-keyset-pagination", do
    let state : Pool.State := { runs := #[{ id := "c" }, { id := "a", mode := .paused }, { id := "b" }] }
    let (_, first) ← unwrap (Pool.command state (.runs none 2))
    let first : Array (String × Pool.Mode) ← unwrap (fromJson? first)
    assertEq first #[("a", .paused), ("b", .active)]
    let (_, second) ← unwrap (Pool.command { state with runs := state.runs.filter (·.id != "a") } (.runs (some "b") 2))
    assertEq (← unwrap (fromJson? (α := Array (String × Pool.Mode)) second)) #[("c", .active)]
    assertTrue (!(Pool.command state (.runs none 1000)).isOk) "Unbounded catalog page accepted"⟩,
  ⟨"deployment-api.client-needs-only-http-and-credential", do
    let action := do
      let connection ← Client.connect "https://cloud.example.test" "CLOUD_TOKEN"
      liftExcept (← Client.call connection (.control "request-1" "run-1" .pause))
      return connection
    let (result, world) := (Cli.runWith clientHost action).run {}
    let connection ← unwrap result
    assertEq connection.deployment "production"
    assertEq world.requests.size 2
    assertTrue (world.requests.all (·.1 == "https://cloud.example.test/deployment")) "Wrong endpoint"
    assertTrue (((toJson connection).compress.splitOn "client-secret").length == 1) "Profile contains secret"⟩,
  ⟨"deployment-api.transport-validation", do
    for url in ["https://cloud.example.test", "https://cloud.example.test/api",
        "http://127.0.0.1:1234", "http://[::1]:1234"] do
      discard <| unwrap (Client.validateUrl url)
    for url in ["http://remote.example.test", "http://localhost.evil.test", "http://127.0.0.1:80@evil.test",
        "https://name:password@cloud.example.test", "https://", "https://cloud.example.test/?token=x",
        "https://cloud.example.test\nheader: value"] do
      assertTrue (!(Client.validateUrl url).isOk) s!"Invalid URL accepted: {url}"⟩,
  ⟨"deployment-api.local-and-remote-use-the-same-client", do
    for url in ["http://127.0.0.1:8080", "https://cloud.example.test"] do
      let action := do
        let connection ← Client.connect url "CLOUD_TOKEN" (some "/client.token")
        liftExcept (← Client.call connection (.control "request-1" "run-1" .pause))
      let (result, world) := (Cli.runWith clientHost action).run {}
      discard <| unwrap result
      assertEq world.requests.size 2
      assertTrue (world.requests.all (·.1 == url ++ "/deployment")) "Client changed transport path"
    let action := Client.connect "http://127.0.0.1:8080" "CLOUD_TOKEN" (some "/missing.token")
    let (result, world) := (Cli.runWith clientHost action).run {}
    assertTrue (!result.isOk && world.requests.isEmpty) "Missing file fell back to ambient token"⟩]

end LeanCloudTests.DeploymentApi
