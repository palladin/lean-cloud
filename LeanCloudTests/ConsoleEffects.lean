import LeanCloudTests.Support
import LeanCloudTests.ConsoleModel

namespace LeanCloudTests
open Lean LeanCloud LeanCloudCli
open ConsoleModel (World Invocation)

private def ctx : Context := ⟨"/work", "lean-cloud-console"⟩
private def info : ProgramInfo :=
  ⟨"squares/v1", "array/nat", "nat/v1", "Square numbers", some (toJson (#[2, 3, 4] : Array Nat)),
    #[⟨"Squares.lean", "cloud {\n  Cloud.pure \"square\" (fun () => 29)\n}", #[⟨"square", 2, 0, 2, 0⟩]⟩]⟩
private def savedRun : Run := ⟨"one", "sha256:pinned", info, info.sampleInput.getD Json.null, defaultWorkerCount⟩
private def has (text fragment : String) : Bool := (text.splitOn fragment).length > 1
private def response (text : String := "") : Except String ProcessOutput := .ok { stdout := text }

/-- Protocol fixtures; unrecognized host processes fail instead of running anything. -/
private def process (completed : Bool) (call : Invocation) : Except String ProcessOutput := do
  unless call.command == "docker" || call.command == "http" do throw "Unexpected executable"
  let args := call.args
  if args[0]? == some "port" then response "127.0.0.1:18080"
  else if args.contains "validate" then
    match Json.parse (call.input.getD "") >>= fromJson? (α := Array Nat) with
    | .ok _ => response
    | .error _ => return { exitCode := 2, stderr := "Invalid numbers" }
  else if args.contains "programs" then response (toJson #[info]).compress
  else if args.contains "outcome" then
    response (toJson (if completed then some (Exit.success (toJson (29 : Nat))) else none)).compress
  else if args.contains "status" then response (toJson ({} : Scheduler.State)).compress
  else if args.contains "result" then response "29"
  else if args.contains "cancel" then
    response (toJson (if completed then Exit.success (toJson (29 : Nat)) else .cancelled "Killed by user")).compress
  else if args[0]? == some "logs" then
    let worker := (args.back?.getD "").splitOn "-" |>.getLast!
    let event : ExecutionEvent := ⟨"boot", 1, 10, worker, some 1, "0:1", "execute", "square", savedRun.id, some "square"⟩
    response ("@lean-cloud " ++ (toJson event).compress ++ "\n")
  else if args[0]? == some "stats" then
    response (Json.mkObj [("Name", toJson (ctx.node "worker1")),
      ("CPUPerc", toJson "10.00%"), ("MemUsage", toJson "1MiB / 2MiB"),
      ("NetIO", toJson "1kB / 2kB"), ("BlockIO", toJson "3kB / 4kB")]).compress
  else if args[0]? == some "ps" then
    response (if args.any (·.startsWith "label=com.docker.compose.service=") then "" else "node1\n")
  else if args.contains "{{if .State.Health}}{{.State.Health.Status}}{{end}}" then
    response (String.intercalate "\n" (List.replicate (args.size - 3) "healthy"))
  else if args[0]? == some "inspect" then
    response (toJson (#["worker1", "worker2", "worker3", "scheduler"].map fun role =>
      Json.mkObj [("Name", toJson ("/" ++ ctx.node role)),
        ("State", Json.mkObj [("Status", toJson "running"), ("StartedAt", toJson "boot")]),
        ("Config", Json.mkObj [("Labels", Json.mkObj [
          ("lean-cloud.role", toJson role)])])])).compress
  else if call.command == "http" then response
  else if args[0]? == some "exec" then response "Filesystem 1024-blocks Used Available Capacity Mounted\ndisk 2048 1024 1024 50% /\n"
  else if args.toList.take 2 == ["container", "inspect"] then return { exitCode := 1 }
  else if args.toList.take 2 == ["image", "inspect"] then
    response (if args.contains "{{index .Config.Labels \"lean-cloud.node\"}}" then "http-inbox-v1" else "sha256:pinned\n")
  else if args[0]? == some "compose" || args[0]? == some "tag" ||
      args[0]? == some "stop" || args[0]? == some "rm" || args[0]? == some "update" ||
      args.toList.take 2 == ["volume", "create"] || args.toList.take 2 == ["volume", "inspect"] || args.contains "submit-entry" ||
      args.toList.take 2 == ["run", "-d"] then response
  else throw s!"Unexpected Docker request: {reprStr args}"

private def base (completed := true) : World :=
  ({ process := process completed : World }.save (ctx.root / "compose.yaml") "services: {}")
    |>.json (ctx.root / "deploy/config.json") Project.defaultConfig
    |>.json (ctx.home / "api.json") (Json.mkObj [("url", toJson "http://127.0.0.1:18080"), ("token", toJson "local-cloud")])

private def deployed (completed := true) : World :=
  (base completed).json (ctx.home / "deployment.json") (Deployment.mk ctx.project savedRun.image #[info] defaultWorkerCount 0)

private def launched (completed := true) : World :=
  (deployed completed).json (ctx.directory savedRun.id / "run.json") savedRun
    |>.json (ctx.directory savedRun.id / "input.json") savedRun.input
    |>.json (ctx.directory savedRun.id / "config.json") Json.null

private def checked (program : Cli α) (world : World) : IO (α × World) := do
  let (result, world) := ConsoleModel.run program world
  return (← unwrap result, world)

/-- Existing combined nodes are real in this model; only new capacity may be
created. Drain acknowledgements can be withheld to exercise interrupted scaling. -/
private def scaleProcess (drained : Bool) (call : Invocation) : Except String ProcessOutput := do
  let args := call.args
  if args.contains "pool-workers" then
    response (toJson ({
      generation := 7, active := some #["worker1"],
      drained := if drained then #["worker2", "worker3"] else #[] } : Pool.Membership)).compress
  else if args.toList.take 2 == ["container", "inspect"] then
    let name := args[2]?.getD ""
    let role := name.drop (ctx.project.length + 1) |>.toString
    if (#["scheduler"] ++ workerNames 3).contains role then
      if args.contains "--format" then response "true"
      else response (toJson #[Json.mkObj [("Image", toJson savedRun.image),
        ("Config", Json.mkObj [("Labels", Json.mkObj [("lean-cloud.project", toJson ctx.project),
          ("lean-cloud.role", toJson role)])])]]).compress
    else pure { exitCode := 1, stderr := "No such container" }
  else if args[0]? == some "start" || args[0]? == some "info" then response
  else process false call

def consoleEffectCases : Array TestCase := #[
  ⟨"console.effects.ps-timestamps-and-offline-timing-snapshot", do
    let timing : LeanCloud.Timing.Run := {
      span := some ⟨86400000, some 86401234⟩, observedMs := 86490000 }
    let initial := { (launched) with
      directories := (launched).directories.push ctx.runs.toString
      process := fun call =>
        if call.args.contains "status" then
          response (toJson ({ timing := some timing } : LeanCloud.Timing.Status)).compress
        else process true call }
    let (_, saved) ← checked (command ctx ["ps"]) initial
    assertTrue (has saved.stdout "STARTED (UTC)" && has saved.stdout "FINISHED (UTC)" &&
      has saved.stdout "1970-01-02 00:00:00" && has saved.stdout "1970-01-02 00:00:01" &&
      has saved.stdout "1.234s") "ps omitted timestamps or used observation time as completion"
    let offline := { saved with stdout := "", process := fun _ => .error "offline" }
    let (_, cached) ← checked (command ctx ["ps"]) offline
    assertTrue (has cached.stdout "1.234s" && has cached.stdout "unavailable")
      "Offline ps discarded its saved times or claimed to be live"⟩,
  ⟨"console.effects.ps-shares-one-status-query-with-timing", do
    let initial := { (launched false) with directories := (launched false).directories.push ctx.runs.toString }
    let (_, world) ← checked (command ctx ["ps"]) initial
    assertEq (world.processes.filter (·.args.contains "status")).size 1
      "ps fetched the same scheduler state twice"
    assertTrue (has world.stdout "running (0/1)") "Missing current scheduler status"⟩,
  ⟨"console.effects.legacy-clean-deploy-command-sequence", do
    let legacy := Project.defaultConfig.setObjVal! "mailboxes" (Json.mkObj [
      ("scheduler", Json.mkObj [("host", toJson "scheduler-mailbox"), ("port", toJson (5672 : Nat))]),
      ("workers", toJson #[Json.mkObj [("worker", toJson "worker1"), ("broker", Json.mkObj [])]])])
    let original := (launched).json (Project.assets ctx / "config.json") legacy
    let (rejected, untouched) := ConsoleModel.run (command ctx ["deploy"]) original
    let .error error := rejected | throw (IO.userError "Silently reused RabbitMQ state")
    assertTrue (has error "'clean', then 'deploy'" && has error "permanently deletes") "Missing actionable reset guidance"
    assertTrue untouched.processes.isEmpty "Legacy rejection changed Docker resources"
    assertEq (untouched.file (Project.assets ctx / "config.json")) (original.file (Project.assets ctx / "config.json"))
    let cleanProcess (call : Invocation) :=
      if call.args.contains "ls" || call.args[0]? == some "ps" then response else process true call
    let (_, cleaned) ← checked (command ctx ["clean"]) { untouched with process := cleanProcess }
    assertTrue (cleaned.file (Project.assets ctx / "config.json")).isNone "Clean retained RabbitMQ configuration"
    assertTrue (cleaned.file (ctx.directory "one" / "run.json")).isNone "Clean retained old runs"
    let (_, fresh) ← checked (command ctx ["deploy", "--workers", "1"])
      { cleaned with process := process true, processes := #[] }
    let (config, _) ← checked (readJson (α := Json) (Project.assets ctx / "config.json")) fresh
    assertEq config (← unwrap (Project.runtimeConfig Project.defaultConfig 1))
    assertEq (fresh.file (ctx.root / "deploy/config.json")) (original.file (ctx.root / "deploy/config.json"))
    assertTrue (!fresh.processes.any (·.args.contains "outcome")) "Fresh deployment attempted to recover deleted runs"
    let (_, running) ← checked (command ctx ["run", "squares", "--id", "new"]) fresh
    let (_, finished) ← checked (command ctx ["result", "new"]) running
    assertTrue (has finished.stdout "29") "Fresh deployment could not run a workflow"⟩,
  ⟨"console.http.rediscovers-port-before-send", do
    let world := (base).json (ctx.home / "api.json") (Json.mkObj [
      ("url", toJson "http://127.0.0.1:19090"), ("token", toJson "local-cloud")])
    let (_, after) ← checked (ctx.execApp #["pool-health", "/etc/lean-cloud/config.json"]) world
    let endpoint ← unwrap (Json.parse ((after.file (ctx.home / "api.json")).getD ""))
    assertEq (endpoint.getObjValAs? String "url").toOption (some "http://127.0.0.1:18080")
    assertEq (after.processes.filter (·.command == "http")).size 1
    assertEq (after.processes[0]?.map (·.args[0]?)) (some (some "port"))⟩,
  ⟨"console.effects.elastic-grow-reuses-existing-nodes", do
    let initial := { (launched false) with process := scaleProcess true, directories := #[ctx.runs.toString] }
    let (_, after) ← checked (command ctx ["scale", "5"]) initial
    let (deployment, _) ← checked ctx.deployment after
    assertEq deployment.workers 5
    assertEq deployment.retainedCount 5
    let created := after.processes.filter (fun call => call.args.toList.take 2 == ["run", "-d"])
    assertEq created.size 2
    assertTrue (created.all (fun call => call.args.contains (ctx.node "worker4") || call.args.contains (ctx.node "worker5")))
      "Scale-up created a scheduler or replaced an existing worker"
    assertTrue (!after.processes.any (fun call => call.args.contains "stop" || call.args.contains "rm" || call.args.contains "build"))
      "Scale-up stopped nodes or rebuilt the application"
    assertEq (after.file (ctx.directory "one" / "run.json")) (initial.file (ctx.directory "one" / "run.json"))
    assertTrue after.locks.isEmpty "Scale-up leaked the deployment lock"⟩,
  ⟨"console.effects.elastic-drain-waits-before-removing", do
    let initial := { (launched false) with process := scaleProcess false }
    let (result, waiting) := ConsoleModel.run (ctx.scale 1) initial
    let .error message := result | throw (IO.userError "Removed workers without a drain acknowledgement")
    assertTrue (has message "Still draining" && has message "scale 1") "Missing retry guidance"
    assertTrue (!waiting.processes.any (fun call => call.args[0]? == some "stop" || call.args[0]? == some "rm"))
      "An executing worker was force-stopped"
    assertTrue waiting.locks.isEmpty "Drain timeout leaked its lock"
    let (_, finished) ← checked (ctx.scale 1) { waiting with process := scaleProcess true, processes := #[] }
    let removed := finished.processes.filter (·.args[0]? == some "rm")
    assertEq (removed.map (·.args.back?)) #[some (ctx.node "worker2"), some (ctx.node "worker3")]
    let (deployment, _) ← checked ctx.deployment finished
    assertEq deployment.retainedCount 3
    assertTrue (!finished.processes.any (fun call => call.args.toList.take 2 == ["volume", "rm"])) "Drain deleted durable data"⟩,
  ⟨"console.effects.invalid-capacity-has-no-effects", do
    for args in [["scale", "-1"], ["scale", "nan"], ["deploy", "--workers"],
        ["deploy", "--workers", "-1"], ["deploy", "--workers", "2", "--workers", "3"]] do
      let (result, world) := ConsoleModel.run (command ctx args) (base)
      assertTrue result.toOption.isNone "Invalid capacity accepted"
      assertTrue world.processes.isEmpty "Invalid capacity changed the deployment"
      assertEq world.files (base).files⟩,
  ⟨"console.effects.deploy-output-flags-and-retained-logs", do
    let noise := "Docker output\n"
    let initial := { (base) with stream := some (fun _ => .ok [
      { stdout := noise.toUTF8, exitCode := some 0 }]) }
    let oldLog := ctx.home / "logs" / "build-42-0.log"
    let initial := initial.save oldLog "previous attempt"
      |>.save (ctx.root / "lean-toolchain") "leanprover/lean4:v4.34.1\n"
    for args in [["deploy"], ["deploy", "-v"], ["deploy", "--verbose"],
      ["deploy", "my_app", "-v"], ["deploy", "--verbose", "my_app"]] do
      let (_, world) ← checked (command ctx args) initial
      let verbose := args.contains "-v" || args.contains "--verbose"
      assertEq (has world.stdout noise) verbose
      assertTrue (has world.stdout "Building worker image" && has world.stdout "Starting blob" &&
        has world.stdout "Logs:") "Missing concise stage/log messages"
      assertEq (world.file oldLog) (some "previous attempt")
      assertEq (world.file (ctx.home / "logs" / "build-42-0-1.log")) (some noise)
      let logs := world.files.filter (fun (path, _) => path.endsWith ".log")
      assertEq logs.size 3 "Build and startup did not each save a new log"
      assertTrue (!world.processes.any (fun call => call.args.contains "--verbose" || (call.args[0]? == some "compose" && call.args.contains "-v")))
        "CLI verbosity flag was passed to Docker"
      if args.contains "my_app" then
        let (app, _) ← checked (Project.load ctx.root) world
        assertEq app.executable "my_app"⟩,
  ⟨"console.effects.failed-build-does-not-start-services", do
    let initial := { (base) with stream := some (fun _ => .ok [
      { stderr := "compiler error\n".toUTF8, exitCode := some 1 }]) }
    let (result, world) := ConsoleModel.run (command ctx ["deploy"]) initial
    let .error error := result | throw (IO.userError "Failed build accepted")
    assertTrue (has error ".log" && has world.stderr "compiler error") "Missing failure details"
    assertTrue (!world.processes.any (·.args.contains "up")) "Started services after build failure"
    assertTrue (world.file (ctx.home / "deployment.json")).isNone "Failed deployment was published"
    assertTrue (!has world.stdout "— done" && world.locks.isEmpty && world.children.isEmpty)
      "Failure was labeled done or leaked resources"⟩,
  ⟨"console.effects.redeploy-after-down-checks-results-after-services", do
    for legacy in [false, true] do
      let old := (launched).json (ctx.home / "deployment.json") (Deployment.mk ctx.project "sha256:previous" #[info] defaultWorkerCount 0)
      let initial := { old with
        directories := old.directories.push ctx.runs.toString
        files := if legacy then old.files else old.files.filter (·.1 != (ctx.directory "one" / "config.json").toString) }
      let (_, world) ← checked ctx.deploy initial
      let some services := world.processes.findIdx? (·.args.contains "up")
        | throw (IO.userError "Did not start services")
      let some outcome := world.processes.findIdx? (·.args.contains "outcome")
        | throw (IO.userError "Did not verify the old result")
      assertTrue (services < outcome) "Migration used the removed network before starting services"
      let call := world.processes[outcome]!
      assertEq call.args[0]? (some "run") "Deployment check depended on a running scheduler"
      let config := if legacy then ctx.directory "one" / "config.json" else ctx.root / "deploy/config.json"
      assertTrue (call.args.contains s!"{config}:/etc/lean-cloud/config.json:ro") "Wrong configuration for saved results"
      let some start := world.processes.findIdx? (·.args.contains "serve-scheduler")
        | throw (IO.userError "Did not start the new nodes")
      assertTrue (outcome < start) "Started new code before validating unfinished runs"
      assertEq (world.file (ctx.directory "one" / "run.json")) (initial.file (ctx.directory "one" / "run.json"))⟩,
  ⟨"console.effects.redeploy-with-legacy-program-metadata", do
    let legacy := Json.mkObj [("entry", toJson info.entry), ("inputSchema", toJson info.inputSchema),
      ("resultSchema", toJson info.resultSchema), ("description", toJson info.description),
      ("sampleInput", toJson info.sampleInput), ("source", Json.mkObj [
        ("file", toJson "Old.lean"), ("text", toJson "cloud { return 29 }"),
        ("sites", toJson #[Json.mkObj [("operation", toJson "exec"), ("line", toJson (1 : Nat))]])])]
    let deployment := (toJson (Deployment.mk ctx.project "sha256:previous" #[info] defaultWorkerCount 0))
      |>.setObjVal! "programs" (toJson #[legacy])
    let initial := (launched).json (ctx.home / "deployment.json") deployment
      |>.json (ctx.directory "one" / "run.json") ((toJson savedRun).setObjVal! "program" legacy)
    let (_, world) ← checked ctx.deploy { initial with directories := initial.directories.push ctx.runs.toString }
    assertTrue (world.processes.any (·.args.contains "outcome")) "Legacy run metadata blocked checking saved results"
    assertTrue (world.processes.any (·.args.contains "serve-scheduler")) "Legacy deployment blocked redeploy"
    let (updated, _) ← checked ctx.deployment world
    assertEq (toJson updated.programs) (toJson #[info]) "Deploy did not save the new program metadata"
    assertEq (world.file (ctx.directory "one" / "run.json")) (initial.file (ctx.directory "one" / "run.json"))
      "Redeploy rewrote historical run metadata"⟩,
  ⟨"console.effects.redeploy-bounds-storage-retries", do
    let old := (launched).json (ctx.home / "deployment.json") (Deployment.mk ctx.project "sha256:previous" #[info] defaultWorkerCount 0)
    let initial := { old with directories := old.directories.push ctx.runs.toString }
    for transient in [false, true] do
      let reason := if transient then "S3 record read failed (HTTP 500)" else "Record does not match its key"
      let handler (call : Invocation) : Except String ProcessOutput :=
        if call.args.contains "outcome" then .ok { exitCode := 1, stderr := reason }
        else process true call
      let (result, world) := ConsoleModel.run ctx.deploy { initial with process := handler }
      let .error error := result | throw (IO.userError "Accepted unreadable saved records")
      assertEq error reason
      let attempts := world.processes.filter (·.args.contains "outcome")
      assertEq attempts.size (if transient then 61 else 1)
      assertEq (world.trace.filter (· == "sleep")).size (if transient then 60 else 0)
      assertEq (world.file (ctx.home / "deployment.json")) (initial.file (ctx.home / "deployment.json"))
      assertTrue (!world.processes.any (·.args.contains "serve-scheduler")) "Unreadable records were bypassed"
      assertTrue world.locks.isEmpty "Storage failure leaked the deployment lock"⟩,
  ⟨"console.effects.redeploy-preserves-unfinished-runs", do
    let old := (launched false).json (ctx.home / "deployment.json") (Deployment.mk ctx.project "sha256:previous" #[info] defaultWorkerCount 0)
    let initial := { old with directories := old.directories.push ctx.runs.toString }
    let (result, world) := ConsoleModel.run ctx.deploy initial
    let .error error := result | throw (IO.userError "Replaced an unfinished run's image")
    assertTrue (has error "Finish or kill one") "Missing recovery guidance"
    assertEq (world.file (ctx.home / "deployment.json")) (initial.file (ctx.home / "deployment.json"))
    assertTrue (!world.processes.any (·.args.contains "serve-scheduler")) "Started new nodes for unfinished work"
    assertTrue world.locks.isEmpty "Redeploy rejection leaked its lock"⟩,
  ⟨"console.effects.redeploy-refuses-missing-durable-data", do
    let handler (call : Invocation) : Except String ProcessOutput :=
      if call.args.toList == ["volume", "inspect", ctx.project ++ "_blob-data"] then
        .ok { exitCode := 1 } else process true call
    let initial := { (deployed) with process := handler }
    let (result, world) := ConsoleModel.run ctx.deploy initial
    assertTrue result.toOption.isNone "Redeploy recreated missing storage"
    assertTrue (!world.processes.any (·.args.contains "up")) "Started services with missing durable data"
    assertEq (world.file (ctx.home / "deployment.json")) (initial.file (ctx.home / "deployment.json"))⟩,
  ⟨"console.effects.pause-resume-and-kill", do
    let initial := launched false
    let (_, paused) ← checked (command ctx ["pause", "one"]) initial
    let (control, _) ← checked (ctx.control "one") paused
    assertTrue (control == .paused) "Pause was not persisted"
    assertEq (paused.processes.filter (·.command == "http") |>.map (·.args.toList)) #[
      ["pause", "/etc/lean-cloud/config.json", "one"]]
    assertTrue (paused.processes.all (fun p => p.command == "http" || p.args[0]? == some "port")) "Pause bypassed HTTP"
    assertEq (paused.file (ctx.directory "one" / "run.json")) (initial.file (ctx.directory "one" / "run.json"))
    let (_, resumed) ← checked (ctx.resume "one") paused
    let (control, _) ← checked (ctx.control "one") resumed
    assertTrue (control == .active) "Resume did not clear pause"
    let (_, killed) ← checked (command ctx ["kill", "one"]) resumed
    let (control, _) ← checked (ctx.control "one") killed
    assertTrue (control == .killed) "Kill was not persisted"
    let (result, blocked) := ConsoleModel.run (ctx.resume "one") killed
    assertTrue result.toOption.isNone "Killed run could be resumed"
    assertEq blocked.processes.size killed.processes.size "Killed run invoked Docker on resume"
    let (_, retried) ← checked (ctx.kill "one") killed
    assertTrue retried.locks.isEmpty "Kill leaked locks"⟩,
  ⟨"console.effects.kill-keeps-completed-result", do
    let (_, world) ← checked (ctx.kill "one") (launched true)
    assertTrue (has world.stdout "already completed") "Kill overwrote normal completion"
    let (control, _) ← checked (ctx.control "one") world
    assertTrue (control == .active) "Completed result was mislabeled killed"
    let (_, inspected) ← checked (command ctx ["inspect", "one"]) { world with
      process := fun call => if call.args.contains "status" then .error "Scheduler stopped" else process true call }
    assertTrue (has inspected.stdout "Outcome: completed") "Completed inspection needed a live scheduler"⟩,
  ⟨"console.effects.interrupted-kill-remains-blocked-and-retryable", do
    let initial := launched false
    let (_, success) ← checked (ctx.kill "one") initial
    for index in [:success.trace.size] do
      if success.trace[index]! == "unlock" then continue
      let (_, interrupted) := ConsoleModel.run (ctx.kill "one") { initial with failAt := some index }
      assertTrue interrupted.locks.isEmpty s!"Kill leaked a lock at {index}"
      let clean := { interrupted with failAt := none }
      let (control, _) ← checked (ctx.control "one") clean
      if control == .killing || control == .killed then
        let (result, _) := ConsoleModel.run (ctx.resume "one") clean
        assertTrue result.toOption.isNone "Interrupted kill allowed resume"
      let (_, retried) ← checked (ctx.kill "one") clean
      let (control, _) ← checked (ctx.control "one") retried
      assertTrue (control == .killed) s!"Retry failed after interruption at {index}"⟩,
  ⟨"console.effects.interrupted-pause-is-retryable", do
    let initial := launched false
    let (_, success) ← checked (ctx.pause "one") initial
    for index in [:success.trace.size] do
      if success.trace[index]! == "unlock" then continue
      let (_, interrupted) := ConsoleModel.run (ctx.pause "one") { initial with failAt := some index }
      assertTrue interrupted.locks.isEmpty s!"Pause leaked a lock at {index}"
      let (_, retried) ← checked (ctx.pause "one") { interrupted with failAt := none }
      let (control, _) ← checked (ctx.control "one") retried
      assertTrue (control == .paused) s!"Pause retry failed at {index}"⟩,
  ⟨"console.effects.control-status-with-unavailable-results", do
    for control in [RunControl.pausing, .paused, .killing, .killed] do
      let initial := (launched false).json (ctx.directory "one" / "control.json") control
      let offline := { initial with
        directories := initial.directories.push ctx.runs.toString
        process := fun call =>
          if call.args.contains "outcome" then .error "Blob service unavailable"
          else if call.args.contains "status" then .error "Scheduler unavailable"
          else process false call }
      for args in [["ps"], ["inspect", "one"], ["watch", "one", "--once"]] do
        let (_, world) ← checked (command ctx args) offline
        assertTrue (has world.stdout control.label) s!"Missing status: {control.label}"
        assertTrue (!world.processes.any (fun call => call.args.contains "resume" || call.args.contains "submit-entry"))
          "Observing control state resumed execution"⟩,
  ⟨"console.effects.resume-uses-existing-pool", do
    let initial := (launched false).json (ctx.directory "one" / "control.json") RunControl.paused
    let (_, resumed) ← checked (ctx.resume "one") initial
    assertTrue (resumed.processes.all (fun p => p.command == "http" || p.args[0]? == some "port")) "Resume changed deployment containers"
    assertTrue (resumed.processes.any (·.args.contains "resume")) "No scheduler resume request"
    let failing (call : Invocation) :=
      if call.args.contains "resume" then .error "Scheduler unavailable" else process false call
    let (result, interrupted) := ConsoleModel.run (ctx.resume "one") { initial with process := failing }
    assertTrue result.toOption.isNone "Resume failure was swallowed"
    let (control, _) ← checked (ctx.control "one") interrupted
    assertTrue (control == .paused) "Failed resume cleared pause intent"⟩,

  ⟨"console.effects.down-preserves-data", do
    let initial := launched
    let (_, world) ← checked (discard (command ctx ["down"])) initial
    assertEq world.files initial.files
    assertEq (world.processes.map (·.args.toList)) #[
      ["ps", "-aq", "--filter", "label=lean-cloud.project=" ++ ctx.project],
      ["stop", "node1"], ["rm", "node1"],
      ["compose", "-p", ctx.project, "-f", "/work/compose.yaml", "down", "--remove-orphans"]]
    assertTrue world.locks.isEmpty "Shutdown leaked a lock"⟩,
  ⟨"console.effects.down-with-no-actors", do
    let handle (call : Invocation) :=
      if call.args[0]? == some "ps" then response else process true call
    let initial := { (deployed) with process := handle }
    let (_, world) ← checked ctx.down initial
    assertEq world.processes.size 2
    assertTrue (world.processes.all (fun call => call.args[0]? != some "stop" && call.args[0]? != some "rm"))
      "Shutdown tried to stop an empty container list"
    let (_, empty) ← checked ctx.down {}
    assertTrue empty.processes.isEmpty "Shutdown of an unconfigured app invoked Docker"⟩,
  ⟨"console.effects.deploy-and-launch", do
    let (_, world) ← checked (do ctx.deploy; ctx.launch "squares" none (some "one")) (base false)
    assertTrue world.locks.isEmpty "Deployment/launch leaked a lock"
    let manifest ← unwrap (Json.parse (world.file (ctx.directory "one" / "run.json")).get! >>= fromJson? (α := Run))
    assertEq manifest.image savedRun.image
    assertEq manifest.input.compress savedRun.input.compress
    let actors := world.processes.filter (·.args.toList.take 2 == ["run", "-d"])
    assertEq actors.size 4
    assertTrue (actors.all (fun call => call.args.contains savedRun.image &&
      !call.args.contains "lean-cloud.run=one")) "Deployment actors must be shared"
    for role in #["scheduler", "worker1", "worker2", "worker3"] do
      let some node := actors.find? (·.args.contains (ctx.node role))
        | throw (IO.userError "Missing combined node")
      assertTrue (node.args.contains (role ++ "-mailbox") &&
        node.args.contains (ctx.project ++ "_" ++ role ++ "-mailbox-data:/mailbox"))
        "Node lost its durable inbox or stable endpoint identity"
    assertTrue (world.processes.any (·.args.contains "lean-cloud-console-app:pinned")) "No retained image tag"
    assertTrue (!world.files.any (fun (path, _) => path.endsWith ".tmp")) "Atomic manifest replacement incomplete"⟩,
  ⟨"console.effects.upgrade-stops-old-nodes-before-reusing-storage", do
    let handler (call : Invocation) := do
      if call.args.toList.take 2 == ["container", "inspect"] then
        let role := (call.args.back?.getD "").splitOn "-" |>.getLast!
        return { stdout := (toJson #[Json.mkObj [
          ("Image", toJson "sha256:old"), ("Config", Json.mkObj [("Labels", Json.mkObj [
            ("lean-cloud.project", toJson ctx.project), ("lean-cloud.role", toJson role)])])]]).compress }
      if call.args[0]? == some "ps" && call.args.any (·.startsWith "label=com.docker.compose.service=") then
        return { stdout := "old-" ++ (call.args.back?.getD "") }
      process true call
    let (_, world) ← checked ctx.deploy { base with process := handler }
    let some stopped := world.processes.findIdx? (fun call => call.args[0]? == some "stop" && call.args.contains (ctx.node "scheduler"))
      | throw (IO.userError "Old actors were not stopped")
    let some removed := world.processes.findIdx? (fun call => call.args[0]? == some "rm" && call.args.contains (ctx.node "scheduler"))
      | throw (IO.userError "Old actors were not removed")
    let some created := world.processes.findIdx? (fun call => call.args.toList.take 2 == ["run", "-d"])
      | throw (IO.userError "Combined actors were not started")
    assertTrue (stopped < removed && removed < created) "Migration overlapped actor ownership"
    assertTrue (!world.processes.any (fun call => call.args.toList.take 2 == ["volume", "rm"]))
      "Migration removed durable storage"⟩,
  ⟨"console.effects.node-readiness-is-required-and-bounded", do
    let handler (call : Invocation) :=
      if call.args.contains "{{if .State.Health}}{{.State.Health.Status}}{{end}}" then response "starting"
      else process true call
    let (result, world) := ConsoleModel.run ctx.deploy { base with process := handler }
    assertTrue result.toOption.isNone "Unhealthy deployment reported success"
    assertTrue (!world.processes.any (·.args.contains "pool-health")) "Contacted scheduler before nodes were ready"
    assertEq (world.trace.filter (· == "sleep")).size 300
    assertTrue world.locks.isEmpty "Startup timeout leaked deployment lock"⟩,
  ⟨"console.effects.reject-before-launch", do
    let input := ctx.root / "bad input.json"
    let (result, world) := ConsoleModel.run (ctx.launch "squares" (some input.toString) (some "one"))
      ((deployed).json input (toJson "invalid"))
    assertTrue result.toOption.isNone "Invalid input accepted"
    assertTrue (world.file (ctx.directory "one" / "run.json")).isNone "Invalid input persisted a run"
    let requests := world.processes.filter (·.command == "http")
    assertEq requests.size 1
    assertEq requests[0]!.input (some "\"invalid\"\n")
    assertTrue world.locks.isEmpty "Input rejection acquired/leaked a lock"⟩,
  ⟨"console.effects.launch-identity-and-resume", do
    let (result, duplicate) := ConsoleModel.run (ctx.launch "squares" none (some "one")) (launched)
    assertTrue result.toOption.isNone "Duplicate run accepted"
    assertTrue duplicate.locks.isEmpty "Duplicate run leaked catalog lock"
    let (_, completed) ← checked (ctx.resume "one") (launched)
    assertTrue (completed.processes.all (·.args.toList.take 2 != ["run", "-d"])) "Completed run restarted"
    let (result, mismatch) := ConsoleModel.run (ctx.resume "one")
      ((launched).json (ctx.directory "one" / "input.json") (toJson (#[100] : Array Nat)))
    assertTrue result.toOption.isNone "Changed run input accepted"
    assertTrue (mismatch.locks.isEmpty && mismatch.processes.isEmpty) "Changed input submitted/leaked lock"⟩,
  ⟨"console.effects.all-inspection-commands", do
    let initial := { (launched) with directories := (launched).directories.push ctx.runs.toString }
    let (_, world) ← checked (do
      for args in [["programs"], ["ps"], ["inspect", "one"], ["result", "one"],
          ["top", "--once"], ["logs", "one", "worker2"], ["watch", "one", "--once"]] do
        discard (command ctx args)) initial
    for text in ["squares/v1", "completed", "LOCATION", "29", "CPU", "Source:"] do
      assertTrue (has world.stdout text) s!"Missing command output: {text}"
    assertTrue (!world.stdout.contains '\x1b' && !world.trace.contains "enterTerminal") "--once entered raw terminal"⟩,
  ⟨"console.effects.terminal-failure-in-every-view-and-offline-last-view", do
    let error : CloudError := ⟨.protocol, "Interpreter fuel exhausted"⟩
    let initial := { (launched false) with
      directories := #[ctx.runs.toString]
      process := fun call =>
        if call.args.contains "outcome" then response (toJson (some (Exit.failure error))).compress
        else if call.args.contains "status" then response (toJson ({ error := some error } : Scheduler.State)).compress
        else process false call }
    for args in [["ps"], ["inspect", "one"], ["result", "one"], ["watch", "one", "--once"]] do
      let (_, world) ← checked (command ctx args) initial
      assertTrue (has world.stdout "failed" && !has world.stdout "result pending") "Terminal error was shown as pending"
      if args != ["ps"] then assertTrue (has world.stdout error.message) "Failure reason missing"
      assertTrue (!world.processes.any (·.args[0]? == some "stats")) "Failed workflow used live worker metrics"
      if args[0]? == some "watch" then
        assertTrue (has world.stdout "LAST VIEW") "Failed workflow still follows live execution"
        for control in [RunControl.active, .pausing, .paused, .killing, .killed] do
          let saved := world.json (ctx.directory "one" / "control.json") control
          let (_, offline) ← checked (command ctx args) { saved with stdout := "", process := fun _ => .error "Offline" }
          assertTrue (has offline.stdout s!"failed: {error.message} (saved)") "Local intent hid the confirmed failure"
    let (result, world) := ConsoleModel.run (ctx.resume "one") initial
    let .error message := result | throw (IO.userError "Resumed a terminal failure")
    assertTrue (has message error.message && has message "new run") "Resume omitted failure guidance"
    assertTrue (!world.processes.any (·.args.contains "resume")) "Resume reached the failed run"⟩,
  ⟨"console.effects.shared-node-traces-stay-with-the-run", do
    let event : ExecutionEvent := ⟨"shared", 1, 1, "worker1", some 0, "0:0", "execute", "other-work", "another", none⟩
    let handle (call : Invocation) := do
      let out ← process true call
      if call.args[0]? == some "logs" then
        return { out with stdout := out.stdout ++ "@lean-cloud " ++ (toJson event).compress ++ "\n" }
      return out
    let initial := { launched with process := handle }
    let (_, world) ← checked (command ctx ["logs", "one"]) initial
    assertTrue (has world.stdout "square" && !has world.stdout "other-work") "Logs crossed workflow boundaries"
    let (snapshot, _) ← checked (LeanCloudCli.Trace.load ctx savedRun) initial
    assertTrue (!snapshot.steps.isEmpty && snapshot.steps.all (·.event.run == savedRun.id))
      "Watch snapshot crossed workflow boundaries"⟩,
  ⟨"console.effects.watch-last-view-offline-and-all-states", do
    for control in [RunControl.active, .paused, .killed] do
      let step : LeanCloudCli.Trace.Step := ⟨"2026-01-01T00:00:00.000000000Z",
        ⟨"boot", 1, 10, "worker1", some 1, "0:1", "execute", "square", savedRun.id, some "square"⟩, none, none, none⟩
      let initial := (launched).json (ctx.directory savedRun.id / "trace.json") #[step]
        |>.json (ctx.directory savedRun.id / "watch-status.json") "completed"
        |>.json (ctx.directory savedRun.id / "control.json") control
      let keys := "\x1b[H\x1b[C\x1b[D\x1b[B\x1b[A\x1b[6~\x1b[5~\x1b[Fq".toUTF8.data.toList.map (·.toUInt32)
      let (_, world) ← checked (command ctx ["watch", "one"]) { initial with
        keys := keys
        process := fun _ => .error "Docker unavailable" }
      assertTrue (world.keys.isEmpty && !world.terminal && world.locks.isEmpty) "Arrow input exited early or leaked terminal/locks"
      assertTrue (has world.stdout "completed (saved)" && has world.stdout "square" && has world.stdout "LAST VIEW")
        "Offline last view lost its status or source"
      assertTrue (world.file (ctx.directory savedRun.id / "trace.json")).isNone "Old execution history was retained"
      assertTrue (world.file (ctx.directory savedRun.id / "watch.json")).isSome "Last view was not saved"
      assertEq (world.processes.filter (·.args[0]? == some "logs")).size 4 "Completed watch kept polling logs"
      assertTrue (world.processes.all fun call => call.args[0]? == some "logs" ||
        call.args[0]? == some "ps" || call.args[0]? == some "port" || call.args.contains "outcome") "Browsing mutated execution"
      assertEq (world.file (ctx.directory savedRun.id / "control.json"))
        (initial.file (ctx.directory savedRun.id / "control.json"))⟩,
  ⟨"console.effects.watch-snapshot-replaces-old-observations", do
    let handler (call : Invocation) := do
      let out ← process true call
      if call.args[0]? != some "logs" then return out
      let worker := (call.args.back?.getD "").splitOn "-" |>.getLast!
      let lines := (Array.range 120).map fun i =>
        let event : ExecutionEvent := ⟨if i < 50 then "old" else "new", i, i, worker, some 1,
          s!"0:{i}", "execute", "square", if i < 110 then savedRun.id else "other", some "square"⟩
        s!"{i + 1000} @lean-cloud " ++ (toJson event).compress
      return { out with stdout := String.intercalate "\n" lines.toList }
    let (snapshot, saved) ← checked (LeanCloudCli.Trace.load ctx savedRun) { launched with process := handler }
    assertEq snapshot.steps.size 1 "The latest branch snapshot retained execution history"
    assertEq (snapshot.steps.back?.map (·.event.seq)) (some 109) "Last observation is from another run or an older attempt"
    assertTrue (saved.processes.all (fun call => !call.args.contains "--tail" && !call.args.contains "--since"))
      "Initial collection lost completed runs or earlier worker incarnations"
    let (again, saved) ← checked (LeanCloudCli.Trace.load ctx savedRun) saved
    assertEq (again.steps.map (·.id)) (snapshot.steps.map (·.id)) "Refresh changed the last snapshot"
    let (offline, _) ← checked (LeanCloudCli.Trace.load ctx savedRun) { saved with process := fun _ => .error "offline" }
    assertEq (offline.steps.map (·.id)) (snapshot.steps.map (·.id)) "Offline view lost its snapshot"
    assertTrue (!offline.warning.isEmpty) "Unavailable observations were not reported"⟩,
  ⟨"console.effects.interactive-repl", do
    let lines := ["unknown\n", "run 'unfinished\n", "help\n", "quit\n", "deploy\n"]
    let initial := { (base) with terminalAvailable := false, lines }
    let (code, world) ← checked (application []) initial
    assertEq code 0
    assertTrue (has world.stderr "Unknown command" && has world.stderr "Unclosed quote") "REPL lost errors"
    assertTrue (has world.stdout "Commands:") "REPL did not continue after errors"
    assertEq world.lines ["deploy\n"]
    assertTrue world.processes.isEmpty "REPL executed after quit"
    let (code, _) ← checked (application []) { (base) with terminalAvailable := false }
    assertEq code 0 "EOF did not exit"
    let (code, _) ← checked (application ["unknown"]) (base)
    assertEq code 1 "One-shot errors must fail"
    let (code, _) ← checked (application ["--help"]) {}
    assertEq code 0 "Help requires a checkout"⟩,
  ⟨"console.effects.live-navigation-and-refresh", do
    let (_, world) ← checked (command ctx ["watch", "one"])
      { (launched false) with keys := [91, 93, 102, 106, 107, 97] ++ List.replicate 10 0 ++ [113] }
    assertTrue (!world.terminal && world.keys.isEmpty) "Watch did not restore terminal or consume keys"
    assertTrue (has world.stdout "BRANCHES") "Branch tree was not rendered"
    assertTrue (has world.stdout "Source:") "Selected branch source was not rendered"
    assertTrue ((world.processes.filter (·.args[0]? == some "stats")).size == 2) "Timed refresh did not resample"
    assertTrue (world.stdout.endsWith "\x1b[?25h\x1b[?1049l") "Watch did not restore display"
    let (_, world) ← checked (command ctx ["watch", "one"]) { (launched) with terminalAvailable := false }
    assertTrue (!world.stdout.contains '\x1b' && !world.trace.contains "key") "Non-TTY watch did not return"⟩,
  ⟨"console.effects.failure-cleanup", do
    -- Inject a failure at every operation of each successful execution. A failure
    -- of release itself is reported, not assumed to have released the resource.
    for (program, initial) in [(ctx.deploy, base), (ctx.down, launched), (ctx.launch "squares" none (some "one"), deployed false),
        (discard (command ctx ["watch", "one"]), launched)] do
      let (_, successful) ← checked program initial
      for index in [:successful.trace.size] do
        let operation := successful.trace[index]!
        if operation == "unlock" || operation == "leaveTerminal" || operation == "closeProcess" then continue
        let (_, world) := ConsoleModel.run program { initial with failAt := some index }
        assertTrue world.locks.isEmpty s!"Lock leaked at {index}: {operation}"
        assertTrue world.children.isEmpty s!"Process leaked at {index}: {operation}"
        assertTrue (!world.terminal) s!"Terminal leaked at {index}: {operation}"⟩,
  ⟨"console.effects.anchored-shell", do
    let keys := "unknown\rhe\t\rqu\t\r".toUTF8.data.toList.map (·.toUInt32)
    let (code, world) ← checked (application []) { (base) with keys, sizes := [(80, 24), (50, 12)] }
    assertEq code 0
    assertTrue (world.keys.isEmpty && !world.terminal) "Shell did not consume input/restore terminal"
    assertTrue (has world.stdout "Unknown command" && has world.stdout "help [COMMAND]") "Command output missing from transcript"
    assertTrue world.stderr.isEmpty "Shell errors bypassed transcript"
    assertTrue (has world.stdout "\x1b[22;1H" && has world.stdout "\x1b[10;1H") "Prompt did not follow terminal resize"
    assertTrue world.processes.isEmpty "Typing/completion ran a Docker process"
    assertTrue (world.stdout.endsWith "\x1b[?1049l") "Shell screen not restored"⟩,
  ⟨"console.effects.shell-watch-handoff", do
    let keys := "watch one\rqquit\r".toUTF8.data.toList.map (·.toUInt32)
    let (_, world) ← checked (application []) { (launched) with keys }
    assertTrue (world.keys.isEmpty && !world.terminal) "Watch did not return to shell"
    assertEq (world.trace.filter (· == "enterTerminal")).size 3
    assertEq (world.trace.filter (· == "leaveTerminal")).size 3
    assertTrue (has world.stdout "Source:" && has world.stdout "[init]") "Watch or shell was not rendered"⟩,
  ⟨"console.effects.shell-failure-cleanup", do
    let initial := { (base) with keys := "deploy\rhelp\rquit\r".toUTF8.data.toList.map (·.toUInt32) }
    let (_, successful) ← checked (application []) initial
    for index in [:successful.trace.size] do
      -- A failed release is observable but cannot be modeled as a successful release.
      if ["leaveTerminal", "unlock", "closeProcess"].contains successful.trace[index]! then continue
      let (_, world) := ConsoleModel.run (application []) { initial with failAt := some index }
      assertTrue (!world.terminal && world.locks.isEmpty && world.children.isEmpty)
        s!"Shell leaked resources at operation {index} ({successful.trace[index]!}); locks={reprStr world.locks}, terminal={world.terminal}, trace={reprStr (world.trace.extract (index - 3) (index + 8))}"⟩,
  ⟨"console.effects.finalizer-error", do
    let program : Cli Unit := do
      try throw "body failure"
      finally request (.write "cleanup")
    let (result, _) := ConsoleModel.run program { failAt := some 0 }
    match result with
    | .error error => assertEq error "injected host failure"
    | .ok _ => assertTrue false "Cleanup failure was swallowed"
    let (result, world) := ConsoleModel.run program {}
    match result with
    | .error error => assertEq error "body failure"
    | .ok _ => assertTrue false "Body failure was swallowed"
    assertEq world.stdout "cleanup"⟩
]

end LeanCloudTests
