import LeanBuild.Batch
import LeanCloud.Source

namespace LeanBuild
open LeanCloud

structure Backend (m : Type → Type) where
  prepare : Environment → Request → m Preparation
  build : Environment → Request → Plan → Array Module → Array BuildResult → m (Array BuildResult)
  finish : Environment → Request → Plan → Array BuildResult → m BuildResult
  check : Environment → Request → Plan → BuildResult → m CheckResult

private def batches [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request) (plan : Plan) :
    Nat → Array Module → Array BuildResult → Cloud m (Array BuildResult)
  | 0, pending, done => pure <| done ++ pending.map fun m =>
      { name := m.name, status := .blocked, message := "Invalid dependency graph" }
  | rounds + 1, pending, done => cloud {
      let (pending, done) := skipBlocked pending done
      if pending.isEmpty then return done
      let groups ← Cloud.parallel fun environment =>
        (partition pending done environment request.modulesPerJob).map fun group => cloud {
          let results ← Cloud.exec (fun executing => backend.build executing request plan group done)
            s!"build {group.size} modules from {(group[0]?.map (·.name)).getD ""}"
          if results.map (·.name) != group.map (·.name) then
            Cloud.fail "Build job returned missing or reordered module results"
          return results
        }
      let results := groups.flatten
      if results.isEmpty then Cloud.fail "No ready modules in a validated plan"
      let completed := results.foldl (fun set r => set.insert r.name) ({} : Std.HashSet String)
      batches backend request plan rounds
        (pending.filter fun m => !completed.contains m.name) (done ++ results)
    }

def workflow [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request) : Cloud m Report := cloud {
  match request.validate with
  | .error reason => Cloud.fail reason
  | .ok () => pure ()
  let prepared ← Cloud.exec (fun env => backend.prepare env request) "fetch and plan"
  let some plan := prepared.plan | return { request, message := prepared.error, build := { name := "prepare", status := .failed, message := prepared.error, diagnostics := prepared.diagnostics } }
  match validateModules plan.modules with
  | .error reason => Cloud.fail reason
  | .ok () => pure ()
  let modules ← batches backend request plan plan.modules.size plan.modules #[]
  let byName := modules.foldl (fun map r => map.insert r.name r) ({} : Std.HashMap String BuildResult)
  let modules := plan.modules.map fun m => byName[m.name]?.getD
    { name := m.name, status := .blocked, message := "Missing module result" }
  let report : Report := {
    request, commit := plan.commit, toolchain := plan.toolchain
    platform := plan.platform, source := some plan.source, modules }
  if modules.any (·.status != .built) then
    return { report with message := "Module build failed; see diagnostics" }
  let build ← Cloud.exec (fun env => backend.finish env request plan modules) "complete Lake targets"
  if build.status != .built then return { report with build, message := "Target build failed" }
  if request.check.mode == .none then
    return { report with
      build, success := true
      message := "Build succeeded; independent verification was not requested" }
  let verification ← Cloud.exec (fun env => backend.check env request plan build) "export and check proofs"
  return { report with
    build, verification := some verification
    success := verification.success, message := if verification.success then "Build and verification succeeded"
      else "Build succeeded; independent verification failed" }
}

end LeanBuild
