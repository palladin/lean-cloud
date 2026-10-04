import LeanCloudCli.Model

namespace LeanCloudCli.Trace
open Lean LeanCloud

/-- Docker timestamps order observations across actors. They are not a causal clock. -/
structure Step where
  timestamp : String
  event : ExecutionEvent
  resources : Option ResourceSample := none
  deriving ToJson

instance : Inhabited Step := ⟨⟨"", ⟨"", 0, 0, "", none, "", "", "", ""⟩, none⟩⟩

/-- Old trace caches remain readable. Absent or malformed telemetry never
fabricates metrics or discards an otherwise valid execution observation. -/
instance : FromJson Step where
  fromJson? json := do
    return { timestamp := ← json.getObjValAs? String "timestamp"
             event := ← json.getObjValAs? ExecutionEvent "event"
             resources := (json.getObjValAs? ResourceSample "resources").toOption }

def Step.id (step : Step) : String :=
  (toJson (step.timestamp, step.event.worker, step.event.session, step.event.seq)).compress

def parse (line : String) : Option Step := do
  let timestamp := if line.startsWith "@lean-cloud " then "" else (line.splitOn " ").head!
  let text := if timestamp.isEmpty then line else (line.drop (timestamp.length + 1)).toString
  let event ← event? text
  let json ← (Json.parse (text.drop 12 |>.toString)).toOption
  return { timestamp, event, resources := (json.getObjValAs? ResourceSample "resources").toOption }

def merge (saved incoming : Array Step) : Array Step := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut steps := #[]
  for step in saved ++ incoming do
    unless seen.contains step.id do
      seen := seen.insert step.id
      steps := steps.push step
  return steps.qsort fun a b =>
    if a.timestamp != b.timestamp then a.timestamp < b.timestamp
    else if a.event.worker != b.event.worker then a.event.worker < b.event.worker
    else if a.event.session != b.event.session then a.event.session < b.event.session
    else a.event.seq < b.event.seq

structure Snapshot where
  steps : Array Step := #[]
  warning : String := ""

/-- Read all retained log segments, including earlier worker incarnations and
runs. Filtering happens after collection; another run never erases this one. -/
def collect (ctx : Context) : Cli Snapshot := do
  let mut steps := #[]
  let mut unavailable := #[]
  let deployment ← try some <$> readJson (α := Deployment) (ctx.home / "deployment.json") catch _ => pure none
  let count := deployment.map (·.retainedCount) |>.getD defaultWorkerCount
  let active := deployment.map (·.workers) |>.getD defaultWorkerCount
  for role in (workerNames count).push "scheduler" do
    let expected := role == "scheduler" || (workerIndex? role).any (· < active)
    let result ← observing (request (.process "docker"
      #["logs", "--timestamps", ctx.project ++ "-" ++ role] none))
    match result with
    | .ok output =>
      if output.exitCode == 0 then
        steps := steps ++ (((output.stdout ++ "\n" ++ output.stderr).splitOn "\n").filterMap parse).toArray
      else if expected then unavailable := unavailable.push role
    | .error _ => if expected then unavailable := unavailable.push role
  return ⟨steps, if unavailable.isEmpty then "" else
    "Logs unavailable for " ++ String.intercalate ", " unavailable.toList ++ "; showing saved observations."⟩

/-- Merge under a per-run lock so simultaneous consoles cannot lose saved steps. -/
def retain (ctx : Context) (run : Run) (incoming : Snapshot) : Cli Snapshot := do
  withLock (ctx.directory run.id / "trace.lock") do
    let path := ctx.directory run.id / "trace.json"
    let saved ← if ← request (.exists path) then readJson path else pure (#[] : Array Step)
    let saved := saved.filter (·.event.run == run.id)
    let steps := merge saved (incoming.steps.filter (·.event.run == run.id))
    if steps.size != saved.size then saveJson path steps
    return { incoming with steps }

def load (ctx : Context) (run : Run) : Cli Snapshot := do
  retain ctx run (← collect ctx)

/-- Capture retained diagnostics after stopping actors, before removing their logs.
Diagnostic failures are reported without blocking deployment control. -/
def archive (ctx : Context) (runs : Array Run) : Cli Unit := do
  if runs.isEmpty then return
  let snapshot ← collect ctx
  for run in runs do
    let result ← observing (retain ctx run snapshot)
    if let .error error := result then printLine s!"Could not save trace for {run.id}: {safe error}"

end LeanCloudCli.Trace
