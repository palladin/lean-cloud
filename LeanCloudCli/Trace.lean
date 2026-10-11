import LeanCloudCli.Model
import LeanCloud.Observations

namespace LeanCloudCli.Trace
open Lean LeanCloud

/-- Shared runtime/client observation format and last-view reduction. -/
abbrev Step := Observations.Step
abbrev location? := Observations.location?
abbrev branch := Observations.branch
abbrev merge := Observations.merge
abbrev latest := Observations.latest

structure Snapshot where
  steps : Array Step := #[]
  warning : String := ""

/-- Keep only the latest view under a per-run lock. -/
def retain (ctx : Context) (run : Run) (incoming : Snapshot) : Cli Snapshot := do
  withLock (ctx.directory run.id / "trace.lock") do
    let path := ctx.directory run.id / "watch.json"
    let saved ← if ← request (.exists path) then readJson path
      else pure (#[] : Array Step)
    let saved := saved.filter (·.event.run == run.id)
    let steps := latest (merge saved (incoming.steps.filter (·.event.run == run.id)))
    if (steps.map (·.id)) != (saved.map (·.id)) || !(← request (.exists path)) then saveJson path steps
    return { incoming with steps }

def load (ctx : Context) (run : Run) : Cli Snapshot := do
  let connection ← ctx.requireConnection
  let mut steps := #[]
  let mut warnings := #[]
  let inventory ← observing (Client.call connection .nodes)
  match inventory with
  | .error _ => warnings := warnings.push "Deployment telemetry unavailable; showing last view."
  | .ok nodes =>
    for node in nodes do
      if !node.online then
        warnings := warnings.push s!"{node.id} unavailable; its last view may be incomplete."
        continue
      try
        let mut after := none
        repeat
          let page ← Client.call connection (.observations run.id node.id after 100)
          unless page.items.all (fun step => step.event.run == run.id && step.event.worker == node.id) do
            throw "Observation identity mismatch"
          steps := steps ++ page.items
          unless page.warning.isEmpty do warnings := warnings.push (node.id ++ ": " ++ page.warning)
          match page.next with
          | none => break
          | some key =>
            unless after.all (· < key) do throw "Non-advancing observation cursor"
            after := some key
      catch _ => warnings := warnings.push (node.id ++ " updates unavailable; showing last view.")
  return ← retain ctx run { steps, warning := String.intercalate "; " warnings.toList }

end LeanCloudCli.Trace
