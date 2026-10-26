import LeanBuild.Model
import LeanCloud.Source

namespace LeanBuild
open LeanCloud

structure Backend (m : Type → Type) where
  prepare : Environment m → Request → m Preparation
  start : Environment m → Plan → m Unit
  builder : Environment m → Request → Plan → m Unit
  results : Environment m → Plan → m (Array BuildResult)
  finish : Environment m → Request → Plan → Array BuildResult → m BuildResult

/-- Prepare once, keep builders alive until the DAG is finished, then assemble
Lake's requested targets. Dependency scheduling is ordinary IO inside builders. -/
def workflow [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request) : Cloud m Report := cloud {
  match request.validate with
  | .error reason => Cloud.fail reason
  | .ok () => pure ()
  let prepared ← Cloud.exec (fun env => backend.prepare env request) "fetch and plan"
  let some plan := prepared.plan | return { request, message := prepared.error, build := { name := "prepare", status := .failed, message := prepared.error, diagnostics := prepared.diagnostics } }
  match validateModules plan.modules with
  | .error reason => Cloud.fail reason
  | .ok () => pure ()
  let count ← Cloud.exec (fun env => do
    backend.start env plan
    pure (max 1 env.workers.size)) "start builders"
  let _ ← Cloud.parallel (label := "Build modules") (completedLabel := "Modules finished") $
    (Array.range (if plan.modules.isEmpty then 0 else count)).map fun _ =>
      Cloud.exec (fun env => backend.builder env request plan) "build modules"
  let modules ← Cloud.exec (fun env => backend.results env plan) "collect module results"
  if modules.map (·.name) != plan.modules.map (·.name) then
    Cloud.fail "Build returned missing or reordered module results"
  let report : Report := {
    request, commit := plan.commit, toolchain := plan.toolchain
    platform := plan.platform, source := some plan.source, modules }
  if modules.any (·.status != .built) then
    return { report with message := "Module build failed; see diagnostics" }
  let build ← Cloud.exec (fun env => backend.finish env request plan modules) "complete Lake targets"
  if build.status != .built then return { report with build, message := "Target build failed" }
  return { report with build, success := true, message := "Build succeeded" }
}

end LeanBuild
