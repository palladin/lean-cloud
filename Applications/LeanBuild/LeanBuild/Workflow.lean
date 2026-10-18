import LeanBuild.Model
import LeanCloud.Source

namespace LeanBuild
open LeanCloud

structure Backend (m : Type → Type) where
  prepare : Request → m Preparation
  build : Request → Plan → Module → Array BuildResult → m BuildResult
  finish : Request → Plan → Array BuildResult → m BuildResult
  check : Request → Plan → BuildResult → m CheckResult

def ready (pending : Array Module) (done : Array BuildResult) : Array Module :=
  pending.filter fun m => m.imports.all fun dep => done.any (·.name == dep)

private def batches [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request) (plan : Plan) :
    Nat → Array Module → Array BuildResult → Cloud m (Array BuildResult)
  | 0, pending, done => pure <| done ++ pending.map fun m =>
      { name := m.name, status := .blocked, message := "Invalid dependency graph" }
  | rounds + 1, pending, done => cloud {
      if pending.isEmpty then return done
      let batch := ready pending done
      if batch.isEmpty then Cloud.fail "No ready modules in a validated plan"
      let results ← Cloud.parallel fun _ => (batch.map fun m => cloud {
        if m.imports.any (fun dep => done.any fun r => r.name == dep && r.status != .built) then
          return { name := m.name, status := .blocked, message := "A prerequisite failed" }
        Cloud.exec (fun _ => backend.build request plan m done) s!"build {m.name}"
      })
      batches backend request plan rounds
        (pending.filter fun m => !batch.any (·.name == m.name)) (done ++ results)
    }

def workflow [Monad m] [MonadCloudExec m] (backend : Backend m) (request : Request) : Cloud m Report := cloud {
  match request.validate with
  | .error reason => Cloud.fail reason
  | .ok () => pure ()
  let prepared ← Cloud.exec (fun _ => backend.prepare request) "fetch and plan"
  let some plan := prepared.plan | return { request, message := prepared.error, build := { name := "prepare", status := .failed, message := prepared.error, diagnostics := prepared.diagnostics } }
  match validateModules plan.modules with
  | .error reason => Cloud.fail reason
  | .ok () => pure ()
  let modules ← batches backend request plan plan.modules.size plan.modules #[]
  let report : Report := {
    request, commit := plan.commit, toolchain := plan.toolchain
    platform := plan.platform, source := some plan.source, modules }
  if modules.any (·.status != .built) then
    return { report with message := "Module build failed; see diagnostics" }
  let build ← Cloud.exec (fun _ => backend.finish request plan modules) "complete Lake targets"
  if build.status != .built then return { report with build, message := "Target build failed" }
  if request.check.mode == .none then
    return { report with
      build, success := true
      message := "Build succeeded; independent verification was not requested" }
  let verification ← Cloud.exec (fun _ => backend.check request plan build) "export and check proofs"
  return { report with
    build, verification := some verification
    success := verification.success, message := if verification.success then "Build and verification succeeded"
      else "Build succeeded; independent verification failed" }
}

end LeanBuild
