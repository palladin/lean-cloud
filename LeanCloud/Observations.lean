import LeanCloud.Telemetry

namespace LeanCloud.Observations
open Lean

/-- Wall-clock timestamps order diagnostic observations across actors. They are not a causal clock. -/
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
    (fun _ => (location? step.event.location).map Observations.branch)

/-- Stable last-view slots. Repeated execution updates a slot instead of
appending history; each parallel call retains its source and child count. -/
def Step.keys (step : Step) : Array String := Id.run do
  let mut keys := #[]
  if let some job := step.job then
    keys := keys.push ("job/" ++ job.branch.key)
    if let .waiting _ := job.status then keys := keys.push ("group/" ++ job.location.key)
  if step.event.worker == "scheduler" then
    if ["paused", "resumed", "sealed", "killed", "failed"].contains step.event.activity then
      keys := keys.push "control"
  else if let some owner := step.owner then
    if step.event.activity == "parallel-label" then
      keys := keys.push ("label/" ++ step.event.location)
    keys := keys.push ("branch/" ++ owner.key)
    if step.event.source.isSome then keys := keys.push ("source/" ++ owner.key)
    if step.event.operation == "parallel" && step.event.source.isSome then
      keys := keys.push ("fork/" ++ step.event.location)
  return keys

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
    let keys := step.keys
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

end LeanCloud.Observations
