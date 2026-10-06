import LeanCloudCli.Model

namespace LeanCloudCli.Trace
open Lean LeanCloud

/-- Docker timestamps order observations across actors. They are not a causal clock. -/
structure Step where
  timestamp : String
  event : ExecutionEvent
  resources : Option ResourceSample := none
  /-- Assignment ownership, distinct from the location currently being replayed. -/
  branch : Option Location := none
  /-- A scheduler observation after persisting a branch transition. -/
  job : Option BranchObservation := none
  deriving ToJson

instance : Inhabited Step := ⟨⟨"", ⟨"", 0, 0, "", none, "", "", "", "", none⟩, none, none, none⟩⟩

/-- Old trace caches remain readable. Absent or malformed telemetry never
fabricates metrics or discards an otherwise valid execution observation. -/
instance : FromJson Step where
  fromJson? json := do
    return { timestamp := ← json.getObjValAs? String "timestamp"
             event := ← json.getObjValAs? ExecutionEvent "event"
             resources := (json.getObjValAs? ResourceSample "resources").toOption
             branch := (json.getObjValAs? Location "branch").toOption
             job := (json.getObjValAs? BranchObservation "job").toOption }

def Step.id (step : Step) : String :=
  (toJson (step.timestamp, step.event.worker, step.event.session, step.event.seq)).compress

def location? (key : String) : Option Location := do
  let parts ← (key.splitOn "/").mapM fun part => do
    match part.splitOn ":" with
    | [child, command] => return (← child.toNat?, ← command.toNat?)
    | _ => none
  let location := parts.toArray
  unless location[0]?.any (·.1 == 0) do none
  return location

def branch (location : Location) : Location :=
  location.set! (location.size - 1) ((location.back?).map (·.1) |>.getD 0, 0)

def Step.owner (step : Step) : Option Location :=
  step.branch.orElse (fun _ => step.job.map (·.branch)) |>.orElse
    (fun _ => (location? step.event.location).map Trace.branch)

def parse (line : String) : Option Step := do
  let timestamp := if line.startsWith "@lean-cloud " then "" else (line.splitOn " ").head!
  let text := if timestamp.isEmpty then line else (line.drop (timestamp.length + 1)).toString
  let event ← event? text
  let json ← (Json.parse (text.drop 12 |>.toString)).toOption
  return { timestamp, event, resources := (json.getObjValAs? ResourceSample "resources").toOption
           branch := (json.getObjValAs? Location "branch").toOption
           job := (json.getObjValAs? BranchObservation "job").toOption }

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

/-- One latest view, not an execution journal: retain each branch's state and
source, each parallel call's source, and a bounded meter window per worker. -/
def latest (steps : Array Step) : Array Step := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut samples : Std.HashMap String (String × Nat) := {}
  let mut kept := #[]
  for step in steps.reverse do
    let mut keys := #[]
    if let some job := step.job then
      keys := keys.push ("job/" ++ job.branch.key)
      if let .waiting _ := job.status then keys := keys.push ("group/" ++ job.location.key)
    if step.event.worker == "scheduler" then
      if ["paused", "resumed", "sealed", "failed"].contains step.event.activity then
        keys := keys.push "control"
    else if let some owner := step.owner then
      keys := keys.push ("branch/" ++ owner.key)
      if step.event.source.isSome then keys := keys.push ("source/" ++ owner.key)
      if step.event.operation == "parallel" && step.event.source.isSome then
        keys := keys.push ("fork/" ++ step.event.location)
    let mut keep := keys.any (!seen.contains ·)
    for key in keys do seen := seen.insert key
    if step.event.worker != "scheduler" then
      if let some sample := step.resources then
        let (incarnation, count) := samples[step.event.worker]?.getD (sample.incarnation, 0)
        if sample.incarnation == incarnation && count < 30 then
          samples := samples.insert step.event.worker (incarnation, count + 1)
          keep := true
    if keep then kept := kept.push step
  return kept.reverse

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
    "Updates unavailable for " ++ String.intercalate ", " unavailable.toList ++ "; showing last view."⟩

/-- Replace the last view under a per-run lock. Old timeline caches are reduced
once and removed; subsequent refreshes never append a replayable history. -/
def retain (ctx : Context) (run : Run) (incoming : Snapshot) : Cli Snapshot := do
  withLock (ctx.directory run.id / "trace.lock") do
    let path := ctx.directory run.id / "watch.json"
    let legacy := ctx.directory run.id / "trace.json"
    let saved ← if ← request (.exists path) then readJson path
      else if ← request (.exists legacy) then readJson legacy else pure (#[] : Array Step)
    let saved := saved.filter (·.event.run == run.id)
    let steps := latest (merge saved (incoming.steps.filter (·.event.run == run.id)))
    if (steps.map (·.id)) != (saved.map (·.id)) || !(← request (.exists path)) then saveJson path steps
    if ← request (.exists legacy) then request (.removeTree legacy)
    return { incoming with steps }

def load (ctx : Context) (run : Run) : Cli Snapshot := do
  retain ctx run (← collect ctx)

/-- Save the last view after stopping actors, before removing their logs.
Diagnostic failures are reported without blocking deployment control. -/
def archive (ctx : Context) (runs : Array Run) : Cli Unit := do
  if runs.isEmpty then return
  let snapshot ← collect ctx
  for run in runs do
    let result ← observing (retain ctx run snapshot)
    if let .error error := result then printLine s!"Could not save last view for {run.id}: {safe error}"

end LeanCloudCli.Trace
