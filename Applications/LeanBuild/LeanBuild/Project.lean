import LeanBuild.BuildError
import LeanBuild.Model
import LeanBuild.Bundle
import LeanEff.Core

namespace LeanBuild.Project
open LeanEff

/-- A typed host boundary shared by the preparation and finalization programs. -/
inductive Host (op : Type → Type) : Effect where
  | request (operation : op α) : Host op (Except BuildError α)

abbrev Program (op : Type → Type) := ExceptT BuildError (EffF (Host op) Empty)

def perform (operation : op α) : Program op α := ExceptT.mk (EffF.send (.request operation))

partial def runWith [Monad m] (handle : {α : Type} → op α → m (Except BuildError α))
    (program : Program op α) : m (Except BuildError α) := do
  match program.run with
  | .pure _ result => return result
  | .impure _ (.request operation) next =>
    runWith handle (ExceptT.mk (next.apply (← handle operation)))

inductive PrepareOp : Type → Type where
  | fetch : PrepareOp String
  | hasSubmodules : PrepareOp Bool
  | checkProject : PrepareOp String
  | discover : PrepareOp (Array Module)
  | snapshot : PrepareOp Bundle.Snapshot
  | platform : PrepareOp String
  | publish (source : Bundle.Snapshot) : PrepareOp FileRef
  | diagnostics : PrepareOp FileRef

/-- Discovery failures are reports; publication failures remain exec failures. -/
def prepareDirectory (commit : String) : Program PrepareOp Preparation := do
  let discovered : Except BuildError (String × String × Array Module × Bundle.Snapshot) ← try
    let toolchain ← perform .checkProject
    let modules ← perform .discover
    liftExcept ((validateModules modules).mapError BuildError.protocol)
    let source ← perform .snapshot
    pure (.ok (toolchain, ← perform .platform, modules, source))
  catch error =>
    match error.primary with
    | .cancelled | .network _ => throw error
    | _ => pure (.error error)
  match discovered with
  | .error error => return { error := toString error, diagnostics := ← perform .diagnostics }
  | .ok (toolchain, platform, modules, snapshot) =>
    let source ← perform (.publish snapshot)
    return { plan := some { commit, toolchain, platform, modules, source } }

def prepare : Program PrepareOp Preparation := do
  let fetched : Except BuildError String ← try pure (.ok (← perform .fetch)) catch error =>
    match error.primary with
    | .cancelled | .network _ => throw error
    | _ => pure (.error error)
  let commit ← match fetched with
    | .ok commit => pure commit
    | .error error => return { error := toString error, diagnostics := ← perform .diagnostics }
  if ← perform .hasSubmodules then
    return { error := "Git submodules are not supported; use Lake dependencies" }
  prepareDirectory commit

inductive FinishOp : Type → Type where
  | now : FinishOp Nat
  | progress (message : String) : FinishOp Unit
  | manifests (references : Array FileRef) : FinishOp (Array Bundle.Manifest)
  | restore (imports : Bundle.Manifest) : FinishOp Bundle.Manifest
  | targets : FinishOp (Array String)
  | difference (baseline : Bundle.Manifest) : FinishOp Bundle.Difference
  | diagnostics : FinishOp FileRef
  | publish (difference : Bundle.Difference) : FinishOp FileRef
  | commit : FinishOp Unit

/-- Restore the module artifacts, finish the requested Lake targets and commit
only a successfully verified and published workspace. -/
def finish (completed : Array BuildResult) : Program FinishOp BuildResult := do
  let start ← perform .now
  perform (.progress "Collecting artifact manifests")
  let references ← completed.mapM fun result => do
    let some ref := result.artifacts | throw (.protocol "Missing prerequisite artifacts")
    return ref
  let imports ← liftExcept ((Bundle.mergeMany (← perform (.manifests references))).mapError BuildError.protocol)
  perform (.progress "Restoring and verifying cached artifacts")
  let baseline ← perform (.restore imports)
  let result : Except BuildError (Array String × Bundle.Difference) ← try
    perform (.progress "Completing Lake targets")
    let names ← perform .targets
    perform (.progress "Verifying final workspace")
    pure (.ok (names, ← perform (.difference baseline)))
  catch error =>
    match error.primary with
    | .cancelled | .network _ => throw error
    | _ => pure (.error error)
  let diagnostics ← perform .diagnostics
  let milliseconds := (← perform .now) - start
  match result with
  | .error message => return { name := "targets", status := .failed, diagnostics, milliseconds, message := toString message }
  | .ok (builtModules, difference) =>
    perform (.progress "Publishing final workspace")
    let artifacts ← perform (.publish difference)
    perform .commit
    perform (.progress "Finished")
    return { name := "targets", status := .built, diagnostics, milliseconds := (← perform .now) - start, artifacts := some artifacts, builtModules }

end LeanBuild.Project
