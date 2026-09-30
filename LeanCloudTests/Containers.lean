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
  ctx.docker (#["compose", "-p", ctx.project] ++ args) check timeout

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
  let worker := ctx.project ++ "-" ++ name
  ctx.workers.modify (·.push worker)
  discard <| ctx.docker #["create", "--network", ctx.project ++ "_default", "--name", worker,
    "-v", s!"{ctx.root / "deploy/config.json"}:{configPath}:ro",
    "lean-cloud-worker:dev", "worker", configPath, run]
  return worker

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
      (report.stderr.splitOn "\n").contains s!"S3 read failed (HTTP {status})"
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
  say s!"Test artifacts retained: {ctx.artifacts}"

def withContext (name : String) (body : Context → IO Unit) : IO Unit := do
  let root ← IO.Process.getCurrentDir
  require (← (root / "compose.yaml").pathExists) "Run from the lean-cloud repository root"
  let started ← IO.monoMsNow
  let ctx : Context := {
    root
    artifacts := ← IO.FS.createTempDir
    project := s!"lean-cloud-{name}-{← IO.Process.getPID}-{started}"
    workers := ← IO.mkRef #[]
    started }
  say s!"Test project: {ctx.project}; artifacts: {ctx.artifacts}"
  try body ctx finally ctx.cleanup

end LeanCloudTests.Containers
