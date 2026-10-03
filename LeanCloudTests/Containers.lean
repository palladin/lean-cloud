import Lean

/-! Docker test infrastructure. The driver owns an isolated Compose project;
the application containers still run the ordinary replay interpreter. -/

namespace LeanCloudTests.Containers
open Lean

def configPath : String := "/etc/lean-cloud/config.json"

structure Context where
  root : System.FilePath
  artifacts : System.FilePath
  project : String
  workers : IO.Ref (Array String)
  nextWorker : IO.Ref Nat
  workerCount : Nat
  started : Nat

def say (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def append (path : System.FilePath) (text : String) : IO Unit :=
  IO.FS.withFile path .append fun handle => handle.putStr text

def Context.event (ctx : Context) (kind : String) (fields : List (String × Json) := []) : IO Unit := do
  let entry := Json.mkObj (("elapsedMs", toJson ((← IO.monoMsNow) - ctx.started)) ::
    ("event", toJson kind) :: fields)
  say entry.compress
  append (ctx.artifacts / "events.jsonl") (entry.compress ++ "\n")

/-- Capture both output streams concurrently so neither pipe can block the CLI.
Timeouts terminate the CLI's process group; container cleanup runs separately. -/
private def output (args : IO.Process.SpawnArgs) (timeout : Nat) : IO IO.Process.Output := do
  let child ← IO.Process.spawn { args with
    stdin := .null
    stdout := .piped
    stderr := .piped
    setsid := true }
  let stdout ← IO.asTask child.stdout.readToEnd .dedicated
  let stderr ← IO.asTask child.stderr.readToEnd .dedicated
  let deadline := (← IO.monoMsNow) + timeout * 1000
  let reaped ← IO.mkRef false
  try
    repeat
      if let some code ← child.tryWait then
        reaped.set true
        return ⟨code, ← IO.ofExcept stdout.get, ← IO.ofExcept stderr.get⟩
      if (← IO.monoMsNow) ≥ deadline then
        throw (IO.userError s!"Command timed out after {timeout}s: {args.cmd}")
      IO.sleep 20
  finally
    if !(← reaped.get) then
      child.kill
      discard child.wait

def Context.docker (ctx : Context) (args : Array String) (check := true)
    (timeout := 60) : IO IO.Process.Output := do
  let command := "docker " ++ String.intercalate " " args.toList
  append (ctx.artifacts / "commands.log") s!"$ {command}\n"
  let result ← output { cmd := "docker", args, cwd := some ctx.root } timeout
  append (ctx.artifacts / "commands.log") (result.stdout ++ result.stderr)
  require (!check || result.exitCode == 0)
    s!"Command failed ({result.exitCode}): {command}\n{result.stdout}{result.stderr}"
  return result

def Context.compose (ctx : Context) (args : Array String) (check := true)
    (timeout := 60) : IO IO.Process.Output :=
  ctx.docker (#["compose", "-p", ctx.project, "-f", (ctx.root / "compose.yaml").toString,
    "-f", (ctx.artifacts / "compose.json").toString] ++ args) check timeout

def Context.brokers (ctx : Context) : Array String :=
  #["scheduler-mailbox"] ++ (Array.range ctx.workerCount).map (fun i => s!"worker{i + 1}-mailbox")

def Context.startServices (ctx : Context) : IO Unit := do
  discard <| ctx.compose (#["up", "-d", "--wait", "blobs"] ++ ctx.brokers) (timeout := 240)

/-- Extend the ordinary deployment with one independent broker per test worker,
including a fresh worker after completion. All resources belong to this project. -/
private def Context.prepare (ctx : Context) : IO Unit := do
  let config ← IO.ofExcept (Json.parse (← IO.FS.readFile (ctx.root / "deploy/config.json")))
  let mailboxes ← IO.ofExcept (config.getObjVal? "mailboxes")
  let broker ← IO.ofExcept (mailboxes.getObjVal? "scheduler")
  let workers := (Array.range ctx.workerCount).map fun i => Json.mkObj [
    ("worker", toJson s!"worker{i + 1}"),
    ("broker", broker.setObjVal! "host" (toJson s!"worker{i + 1}-mailbox"))]
  let config := config.setObjVal! "mailboxes" (mailboxes.setObjVal! "workers" (toJson workers))
  IO.FS.writeFile (ctx.artifacts / "config.json") config.pretty
  -- Use the actual Compose broker definition, including its image and settings.
  let base ← ctx.docker #["compose", "-f", (ctx.root / "compose.yaml").toString, "config", "--format", "json"]
  let base ← IO.ofExcept (Json.parse base.stdout)
  let template ← IO.ofExcept ((base.getObjVal? "services") >>= (·.getObjVal? "worker1-mailbox"))
  let configVolume := toJson #[s!"{ctx.artifacts / "config.json"}:{configPath}:ro"]
  let mut services := ["worker", "worker2", "worker3", "submit", "scheduler", "checks"].map fun name =>
    (name, Json.mkObj [("volumes", configVolume)])
  let mut volumes := []
  for i in [3:ctx.workerCount] do
    let name := s!"worker{i + 1}-mailbox"
    let volume := name ++ "-data"
    let node := (template.setObjVal! "hostname" (toJson name)).setObjVal! "volumes" (toJson #[
      s!"{volume}:/var/lib/rabbitmq", s!"{ctx.root / "deploy/rabbitmq.conf"}:/etc/rabbitmq/rabbitmq.conf:ro"])
    services := services ++ [(name, node)]
    volumes := volumes ++ [(volume, Json.mkObj [])]
  IO.FS.writeFile (ctx.artifacts / "compose.json") (Json.mkObj [
    ("services", Json.mkObj services), ("volumes", Json.mkObj volumes)]).pretty

structure Status where
  running : Bool
  exitCode : Nat
  deriving Repr

def Context.status (ctx : Context) (worker : String) : IO Status := do
  let result ← ctx.docker #["inspect", "--format", "{{json .State}}", worker]
  let parsed : Except String Status := do
    let json ← Json.parse result.stdout
    return {
      running := ← json.getObjValAs? Bool "Running"
      exitCode := ← json.getObjValAs? Nat "ExitCode" }
  IO.ofExcept parsed

def checkExit (worker : String) (status : Status) : IO Unit :=
  require (status.running || status.exitCode == 0)
    s!"Unplanned worker failure: {worker} exited {status.exitCode}"

def Context.createWorker (ctx : Context) (name run : String) : IO String := do
  let index ← ctx.nextWorker.get
  require (index < ctx.workerCount) "No independent broker reserved for this worker"
  ctx.nextWorker.set (index + 1)
  let worker := ctx.project ++ "-" ++ name
  ctx.workers.modify (·.push worker)
  discard <| ctx.docker #["create", "--network", ctx.project ++ "_default", "--name", worker,
    "-e", s!"CLOUD_WORKER_ID=worker{index + 1}",
    "-v", s!"{ctx.artifacts / "config.json"}:{configPath}:ro",
    "lean-cloud-worker:dev", "worker", configPath, run]
  return worker

def Context.createScheduler (ctx : Context) (name run : String) : IO String := do
  let scheduler := ctx.project ++ "-" ++ name
  ctx.workers.modify (·.push scheduler)
  discard <| ctx.docker #["create", "--network", ctx.project ++ "_default", "--network-alias", "scheduler",
    "--name", scheduler, "-v", s!"{ctx.artifacts / "config.json"}:{configPath}:ro",
    "-v", ctx.project ++ "_scheduler-data:/data", "lean-cloud-worker:dev", "scheduler", configPath, run]
  discard <| ctx.docker #["start", scheduler]
  let deadline := (← IO.monoMsNow) + 30000
  repeat
    let result ← ctx.docker #["exec", scheduler, "cloud-demo", "status", configPath, run] (check := false)
    if result.exitCode == 0 then return scheduler
    require ((← IO.monoMsNow) < deadline) "Scheduler did not become ready"
    IO.sleep 200

def Context.start (ctx : Context) (workers : Array String) : IO Unit := do
  discard <| ctx.docker (#["start"] ++ workers)

def Context.logs (ctx : Context) (worker : String) : IO String :=
  return (← ctx.docker #["logs", worker]).stdout

/-- False means normal completion raced with injection. Every reported crash
must be an observed SIGKILL, never an infrastructure error or normal exit. -/
def Context.crash (ctx : Context) (worker : String) : IO Bool := do
  let status ← ctx.status worker
  checkExit worker status
  if !status.running then return false
  let result ← ctx.docker #["kill", "--signal", "KILL", worker] (check := false)
  let status ← ctx.status worker
  if !status.running && status.exitCode == 0 then return false
  require (result.exitCode == 0 && !status.running && status.exitCode == 137)
    s!"Expected SIGKILL exit 137 for {worker}; got {reprStr status}\n{result.stderr}"
  return true

def Context.waitAll (ctx : Context) (workers : Array String) (timeout := 120) : IO Unit := do
  let deadline := (← IO.monoMsNow) + timeout * 1000
  repeat
    let mut running := false
    for worker in workers do
      let status ← ctx.status worker
      checkExit worker status
      running := running || status.running
    if !running then return
    require ((← IO.monoMsNow) < deadline) "Workers did not finish after faults stopped"
    IO.sleep 200

/-- After a service restart, S3 may accept connections before its volumes are
available. Only temporary S3 read errors may be retried; missing or corrupt data
and incorrect reports always fail immediately. -/
def Context.checkReport (ctx : Context) (run expected : String)
    (restartTimeout : Nat := 0) : IO Unit := do
  let deadline := (← IO.monoMsNow) + restartTimeout * 1000
  repeat
    let report ← ctx.compose #["run", "--rm", "--no-deps", "worker", "result", configPath, run]
      (check := false)
    if report.exitCode == 0 then
      let actual := report.stdout.trimAscii.toString
      require (actual == expected) s!"Wrong durable report. Expected {expected}; got {actual}"
      return
    let temporary := [500, 502, 503, 504].any fun status =>
      ["S3 read", "S3 record read"].any fun operation =>
        (report.stderr.splitOn "\n").contains s!"{operation} failed (HTTP {status})"
    require (temporary && (← IO.monoMsNow) < deadline)
      s!"Cannot read durable report ({report.exitCode}): {report.stdout}{report.stderr}"
    say s!"S3 is recovering after restart; retrying report {run}."
    IO.sleep 1000

private def bestEffort (action : IO Unit) : IO Unit := do
  try action catch error => IO.eprintln s!"Cleanup/diagnostic failure: {error}"

private def Context.cleanup (ctx : Context) : IO Unit := do
  let workers ← ctx.workers.get
  for worker in workers do
    bestEffort do
      let logs ← ctx.docker #["logs", "--timestamps", worker] (check := false)
      IO.FS.writeFile (ctx.artifacts / (worker ++ ".log")) (logs.stdout ++ logs.stderr)
  bestEffort do
    let logs ← ctx.compose #["logs", "--no-color", "--timestamps"] (check := false)
    IO.FS.writeFile (ctx.artifacts / "services.log") (logs.stdout ++ logs.stderr)
  if !workers.isEmpty then
    bestEffort do discard <| ctx.docker (#["rm", "-f"] ++ workers)
  bestEffort do
    discard <| ctx.compose #["down", "-v", "--remove-orphans"] (timeout := 120)
  -- createScheduler uses `docker create`, so Compose does not own this volume.
  bestEffort do
    discard <| ctx.docker #["volume", "rm", ctx.project ++ "_scheduler-data"] (check := false)
  say s!"Test artifacts retained: {ctx.artifacts}"

def withContext (name : String) (body : Context → IO Unit) (workers : Nat := 3) : IO Unit := do
  let root ← IO.Process.getCurrentDir
  require (← (root / "compose.yaml").pathExists) "Run from the lean-cloud repository root"
  let started ← IO.monoMsNow
  let ctx : Context := {
    root
    artifacts := ← IO.FS.createTempDir
    project := s!"lean-cloud-{name}-{← IO.Process.getPID}-{started}"
    workers := ← IO.mkRef #[]
    nextWorker := ← IO.mkRef 0
    workerCount := max 3 (workers + 1)
    started }
  say s!"Test project: {ctx.project}; artifacts: {ctx.artifacts}"
  ctx.prepare
  try body ctx finally ctx.cleanup

end LeanCloudTests.Containers
