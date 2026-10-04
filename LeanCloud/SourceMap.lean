import LeanCloud.SourceInfo
import Lean.Elab.Term

namespace LeanCloud
register_option cloud.captureSource : Bool := {
  defValue := false
  descr := "Capture source metadata while elaborating a cloud block" }

end LeanCloud

namespace LeanCloud.SourceMap
open Lean Elab Term

deriving instance ToExpr for SourceSite
deriving instance ToExpr for ProgramSource

private def addSource (sources : Array ProgramSource) (entry : ProgramSource) : Array ProgramSource :=
  match sources.findIdx? (·.file == entry.file) with
  | none => sources.push entry
  | some i => sources.modify i fun source =>
    { source with sites := entry.sites.foldl (fun sites site =>
        if sites.any (·.id == site.id) then sites else sites.push site) source.sites }

initialize extension : SimplePersistentEnvExtension ProgramSource (Array ProgramSource) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addSource
    addImportedFn := fun entries => entries.foldl (fun sources es => es.foldl addSource sources) #[] }

/-- Capture original UTF-8 offsets and the exact compiler input, never search text. -/
def capture (stx : Syntax) : TermElabM (Option SourceSiteId) := do
  let fileMap ← getFileMap
  let some start := stx.getPos? | return none
  let some stop := stx.getTailPos? | return none
  let first := fileMap.toPosition start
  let last := fileMap.toPosition stop
  let module := (← getEnv).mainModule.toString
  let id := s!"{module}:{hash fileMap.source}:{start.byteIdx}:{stop.byteIdx}"
  let site : SourceSite := ⟨id, first.line, first.column, last.line, last.column⟩
  modifyEnv fun env => extension.addEntry env {
    file := module.replace "." "/" ++ ".lean", text := fileMap.source, sites := #[site] }
  return some id

/-- Evaluated at registration, including source maps from imported workflow modules. -/
elab "cloud_sources%" : term => do
  let sources := extension.getState (← getEnv)
  return toExpr sources

end LeanCloud.SourceMap
