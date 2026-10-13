import LeanVerify.Model
import LeanCloud.Source

namespace LeanVerify
open LeanCloud

structure Backend (m : Type → Type) where
  prepare : Request → m Preparation
  check : Request → Plan → Module → Array ModuleResult → m ModuleResult

/-- Ready modules share completed immutable inputs. No branch depends on a result
from its own batch. Failed prerequisites block descendants, not unrelated modules. -/
def ready (pending : Array Module) (done : Array ModuleResult) : Array Module :=
  pending.filter fun m => m.imports.all fun dep =>
    done.any fun result => result.name == dep

private def batches [Monad m] (backend : Backend m) (request : Request) (plan : Plan) :
    Nat → Array Module → Array ModuleResult → Cloud m (Array ModuleResult)
  | 0, pending, done => pure <| done ++ pending.map fun m =>
      { name := m.name, status := .blocked, message := "Invalid dependency graph" }
  | rounds + 1, pending, done => cloud {
      if pending.isEmpty then return done
      let batch := ready pending done
      if batch.isEmpty then Cloud.fail "No ready modules in a validated plan"
      let results ← Cloud.parallel (batch.map fun m => cloud {
        if m.imports.any (fun dep => done.any fun r => r.name == dep && r.status != .checked) then
          return { name := m.name, status := .blocked, message := "A prerequisite failed" }
        Cloud.exec (fun _ => backend.check request plan m done) s!"check {m.name}"
      })
      batches backend request plan rounds
        (pending.filter fun m => !batch.any (·.name == m.name)) (done ++ results)
    }

def workflow [Monad m] (backend : Backend m) (request : Request) : Cloud m Report := cloud {
  match request.validate with
  | .error reason => Cloud.fail reason
  | .ok () => pure ()
  let prepared ← Cloud.exec (fun _ => backend.prepare request) "fetch and plan"
  let some plan := prepared.plan | return {
    repository := request.repository, revision := request.revision
    allowedAxioms := request.allowedAxioms, paranoid := request.paranoid
    message := prepared.error
    modules := #[{ name := "prepare", status := .failed, diagnostics := prepared.diagnostics
                   message := prepared.error }] }
  match validateModules plan.modules with
  | .error reason => Cloud.fail reason
  | .ok () => pure ()
  let results ← batches backend request plan plan.modules.size plan.modules #[]
  let found := results.flatMap (·.theorems.map (·.name))
  let missing := request.theorems.filter (!found.contains ·)
  let success := results.all (·.status == .checked) && missing.isEmpty &&
    request.modules.all (fun name => results.any fun r => r.name == name && r.status == .checked)
  return {
    repository := request.repository, revision := request.revision
    commit := plan.commit, toolchain := plan.toolchain, success, modules := results
    source := plan.source, allowedAxioms := request.allowedAxioms
    paranoid := request.paranoid
    message := if !missing.isEmpty then s!"Missing theorem(s): {String.intercalate ", " missing.toList}"
      else if success then "All requested modules and theorems checked"
      else "Verification failed; see module diagnostics" }
}

end LeanVerify
