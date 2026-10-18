import LeanCloud.SourceInfo
import Lean.Elab.Term
import Lean.Util.FindExpr
import Lean.Compiler.Old
import Lean.Compiler.ImplementedByAttr
import Lean.Meta.LitValues
import Lean.Meta.Reduce

namespace LeanCloud
register_option cloud.captureSource : Bool := {
  defValue := false
  descr := "Capture source metadata while elaborating a cloud block" }

declare_syntax_cat cloudFuncOption
syntax "(" &"descr" " := " str ")" : cloudFuncOption
syntax "(" &"opaque" " := " ident ")" : cloudFuncOption
syntax (name := cloud_func) "cloud_func" cloudFuncOption* : attr

open Lean in
initialize cloudFunc : ParametricAttribute CloudFunctionInfo ←
  registerParametricAttribute {
    name := `cloud_func
    descr := "Describe a Cloud helper and control whether watch shows its implementation"
    getParam := fun name stx => do
      let `(attr| cloud_func $options:cloudFuncOption*) := stx
        | throwError "Invalid cloud_func attribute"
      let name := (privateToUserName name).toString
      let mut info : CloudFunctionInfo := { name, descr := name }
      let mut seenDescr := false
      let mut seenOpaque := false
      for option in options do
        match option with
        | `(cloudFuncOption| (descr := $value:str)) =>
          if seenDescr then throwErrorAt option "Duplicate cloud_func descr"
          if value.getString.trimAscii.isEmpty then throwErrorAt value "Cloud function description cannot be empty"
          seenDescr := true
          info := { info with descr := value.getString }
        | `(cloudFuncOption| (opaque := $value:ident)) =>
          if seenOpaque then throwErrorAt option "Duplicate cloud_func opaque"
          unless value.getId == `true || value.getId == `false do
            throwErrorAt value "Cloud function opaque must be true or false"
          seenOpaque := true
          info := { info with «opaque» := value.getId == `true }
        | _ => throwErrorAt option "Invalid cloud_func option"
      return info }

end LeanCloud

namespace LeanCloud.SourceMap
open Lean Elab Term

deriving instance ToExpr for CloudFunctionInfo
deriving instance ToExpr for SourceSite
deriving instance ToExpr for ProgramSource

private def addSource (sources : Array ProgramSource) (entry : ProgramSource) : Array ProgramSource :=
  match sources.findIdx? (·.file == entry.file) with
  | none => sources.push entry
  | some i => sources.modify i fun source =>
    { source with sites := entry.sites.foldl (fun sites site =>
        match sites.findIdx? (·.id == site.id) with
        | none => sites.push site
        | some i => sites.modify i fun old =>
            { site with functionInfo := site.functionInfo.orElse (fun _ => old.functionInfo) }) source.sites }

initialize extension : SimplePersistentEnvExtension ProgramSource (Array ProgramSource) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := addSource
    addImportedFn := fun entries => entries.foldl (fun sources es => es.foldl addSource sources) #[] }

/-- Capture original UTF-8 offsets and the exact compiler input, never search text. -/
def capture (stx : Syntax) (functionInfo : Option CloudFunctionInfo := none) : TermElabM (Option SourceSiteId) := do
  let fileMap ← getFileMap
  let some start := stx.getPos? | return none
  let some stop := stx.getTailPos? | return none
  let first := fileMap.toPosition start
  let last := fileMap.toPosition stop
  let module := (← getEnv).mainModule.toString
  let id := s!"{module}:{hash fileMap.source}:{start.byteIdx}:{stop.byteIdx}"
  let site : SourceSite := {
    id, line := first.line, column := first.column, endLine := last.line, endColumn := last.column, functionInfo }
  modifyEnv fun env => extension.addEntry env {
    file := module.replace "." "/" ++ ".lean", text := fileMap.source, sites := #[site] }
  return some id

/-- Reduce aliases before identifying a Cloud result. -/
def isCloudType (type : Expr) : MetaM Bool := do
  let type ← Meta.whnf type
  return type.isAppOfArity `LeanEff.EffF 3 &&
    type.getAppArgs[0]!.getAppFn.isConstOf `LeanCloud.Control

private def unionSites (left right : Array SourceSiteId) : Array SourceSiteId :=
  right.foldl (fun sites site => if sites.contains site then sites else sites.push site) left

private def stringLiteral? : Expr → Option String
  | .lit (.strVal value) => some value
  | _ => none

/-- Collect effective sites, composing existing source maps rather than retaining
their superseded inputs. The cache also breaks recursive-definition cycles. -/
private partial def helperSites (name : Name) :
    StateT (NameMap (Array SourceSiteId)) TermElabM (Array SourceSiteId) := do
  if let some sites := (← get).find? name then return sites
  modify (·.insert name #[])
  let env ← getEnv
  let some info := env.find? name | return #[]
  -- Containers and callbacks can hold Cloud computations too. Reduce their type
  -- aliases, without unfolding or running the computation itself.
  let type ← Meta.reduce info.type (explicitOnly := false) (skipTypes := false)
  unless (type.find? fun e => e.isAppOfArity `LeanEff.EffF 3 &&
      e.getAppArgs[0]!.getAppFn.isConstOf `LeanCloud.Control).isSome do return #[]
  -- Partial definitions have a separate executable body. Inspect it without
  -- evaluating it; following the logical opaque constant would miss its sites.
  let implementation ← match Compiler.getImplementedBy? env name with
    | some implementation => helperSites implementation
    | none => pure #[]
  let executable := (env.find? (Compiler.mkUnsafeRecName name)).getD info
  let some body := executable.value? | return implementation
  let known := extension.getState env |>.flatMap (·.sites.map (·.id))
  let rec visit (e : Expr) : StateT (NameMap (Array SourceSiteId)) TermElabM (Array SourceSiteId) := do
    if e.isAppOfArity `LeanCloud.Cloud.withSource 5 then
      let args := e.getAppArgs
      if let some site := stringLiteral? args[2]! then
        if !args[4]!.hasLooseBVars then
          let mapping ← Meta.getArrayLitOf? args[4]! fun pair => do
            if pair.isAppOfArity ``Prod.mk 4 then
              return (·, ·) <$> stringLiteral? pair.getAppArgs[2]! <*> stringLiteral? pair.getAppArgs[3]!
            return none
          if let some mapping := mapping then
            let sites ← visit args[3]!
            let mapped := sites.map fun id => (mapping.find? (·.1 == id)).map (·.2) |>.getD id
            return unionSites (if known.contains site then #[site] else #[]) mapped
    match e with
    | .lit (.strVal site) =>
      return if known.contains site then #[site] else #[]
    | .const name _ => helperSites name
    | .app f a => return unionSites (← visit f) (← visit a)
    | .lam _ _ body _ | .forallE _ _ body _ => visit body
    | .letE _ _ value body _ => return unionSites (← visit value) (← visit body)
    | .mdata _ e | .proj _ _ e => visit e
    | _ => pure #[]
  let sites := unionSites implementation (← visit body)
  modify (·.insert name sites)
  return sites

/-- Give each helper call distinct display IDs, even without an attribute. This
keeps caller-supplied computations separate from the same helper used internally.
An opaque function collapses its implementation to its caller's location. -/
def functionSites (name : Name) (stx : Syntax) (info : Option CloudFunctionInfo) :
    TermElabM (Option (SourceSiteId × Array (SourceSiteId × SourceSiteId))) := do
  let owned := (← (helperSites name).run {}).1
  if owned.isEmpty && info.isNone then return none
  let some caller ← capture stx info | return none
  if info.any (·.opaque) then return some (caller, owned.map (·, caller))
  let sources := extension.getState (← getEnv)
  let mut mapping := #[]
  for source in sources do
    let mut sites := #[]
    for site in source.sites do
      if owned.contains site.id then
        let id := s!"{site.id}:call:{caller}"
        mapping := mapping.push (site.id, id)
        sites := sites.push { site with id, functionInfo := site.functionInfo.orElse (fun _ => info) }
    if !sites.isEmpty then
      modifyEnv fun env => extension.addEntry env { source with sites }
  return some (caller, mapping)

/-- Evaluated at registration, including source maps from imported workflow modules. -/
elab "cloud_sources%" : term => do
  let sources := extension.getState (← getEnv)
  return toExpr sources

end LeanCloud.SourceMap
