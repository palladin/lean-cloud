import LeanBuild.Batch
import LeanCloud.Source

namespace LeanBuild
open LeanCloud

structure Backend (m : Type → Type) where
  prepare : Environment m → Request → m Preparation
  build : Environment m → Request → Plan → Array Module → Array BuildResult → m (Array BuildResult)
  finish : Environment m → Request → Plan → Array BuildResult → m BuildResult

/-- Completed modules at the start of this parallel round. -/
def progressLabel (completed total : Nat) : String :=
  let number (n : Nat) := String.ofList <| (toString n).toList.reverse.zipIdx.foldl
    (fun text (digit, index) => digit :: (if index > 0 && index % 3 == 0 then ',' :: text else text)) []
  s!"{number completed}/{number total} · {completed * 100 / total}%"

private def batches [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request) (plan : Plan) :
    Nat → Array Module → Array BuildResult → Cloud m (Array BuildResult)
  | 0, pending, done => pure <| done ++ pending.map fun m =>
      { name := m.name, status := .blocked, message := "Invalid dependency graph" }
  | rounds + 1, pending, done => cloud {
      let (pending, done) := skipBlocked pending done
      if pending.isEmpty then return done
      let cpus ← Cloud.exec (fun env => pure <|
        (if env.workers.isEmpty then #[env.currentWorker] else env.workers).map (max 1 ·.cpus)) "plan build round"
      let groups ← Cloud.parallel (label := progressLabel done.size plan.modules.size) $
        ((partition pending done cpus request.modulesPerJob).filter (!·.isEmpty)).map fun group => cloud {
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
  return { report with build, success := true, message := "Build succeeded" }
}

end LeanBuild
