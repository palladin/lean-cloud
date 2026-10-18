import LeanCloud.Control
import LeanCloud.SourceMap
import Lean.Elab.BuiltinDo
import Lean.Elab.App

universe u

namespace LeanCloud
open Lean LeanEff

/-- The cloud monad uses lean-eff's shared core with one higher-order effect family. -/
abbrev Cloud (m : Type → Type u) := EffF (Control m) SourceSiteId

variable {m : Type → Type u}

namespace Cloud

private def displaySource (site : SourceSiteId) (remap : Array (SourceSiteId × SourceSiteId))
    (info : Option SourceSiteId) : Option SourceSiteId :=
  some (info.map (fun id => (remap.find? (·.1 == id)).map (·.2) |>.getD id) |>.getD site)

mutual
  /-- Supply a call site to unannotated nodes and remap helper-owned sites.
  Other inner cloud blocks retain their sites. Continuations stay delayed. -/
  def withSource {m : Type → Type u} {α : Type} (site : SourceSiteId)
      (program : Cloud m α) (remap : Array (SourceSiteId × SourceSiteId) := #[]) : Cloud m α :=
    match program with
    | .pure info value => .pure (displaySource site remap info) value
    | .impure info request next => .impure (displaySource site remap info)
        (sourceControl site request remap) (sourceContinuation site next remap)
  termination_by structural program

  def sourceControl {m : Type → Type u} {α : Type} (site : SourceSiteId)
      (request : Control m α) (remap : Array (SourceSiteId × SourceSiteId) := #[]) : Control m α :=
    match request with
    | .parallel codec count branches => .parallel codec count fun i => withSource site (branches i) remap
    | other => other
  termination_by structural request

  def sourceContinuation {m : Type → Type u} {α β : Type} (site : SourceSiteId)
      (next : ArrsF (Control m) SourceSiteId α β)
      (remap : Array (SourceSiteId × SourceSiteId) := #[]) : ArrsF (Control m) SourceSiteId α β :=
    match next with
    | .one k => .one fun value => withSource site (k value) remap
    | .append first rest => .append (sourceContinuation site first remap) (sourceContinuation site rest remap)
  termination_by structural next
end

def send (request : Control m α) : Cloud m α := EffF.send request

def delay (body : Unit → Cloud m α) : Cloud m α := send Control.delay >>= body

def fail (message : String) : Cloud m α := send (.fail ⟨.application, message⟩)

/-- Run with this attempt's worker environment; record only the outcome.
An uncaught computation exception is a recorded failure. To recover or retry,
handle the exception inside `body`; only node crashes trigger replay recovery. -/
def exec [MonadCloudExec m] [Codec α] (body : Environment → m α) (label : String := "") : Cloud m α :=
  send (.command inferInstance (.exec label fun environment => MonadCloudExec.capture (body environment)))

private def fork [Codec α] (branches : Array (Cloud m α)) : Cloud m (Array α) :=
  send (.parallel inferInstance branches.size (fun index => branches[index]))

/-- Record the planning environment before creating branches. Reconstructing any
child uses the same snapshot, even after pool membership or worker capacity changes. -/
def parallel [Pure m] [Codec α]
    (plan : Environment → Array (Cloud m α)) : Cloud m (Array α) := do
  let environment ← send (.command (inferInstance : Codec Environment)
    (.exec "parallel" fun environment => ExceptT.mk (Pure.pure (.ok environment))))
  fork (plan environment)

/-- Heterogeneous pairing uses the same collection-parallel primitive. -/
def both [Codec α] [Codec β] (left : Cloud m α) (right : Cloud m β) : Cloud m (α × β) := do
  let values ← fork #[Sum.inl <$> left, Sum.inr <$> right]
  match values.toList with
  | [.inl a, .inr b] => return (a, b)
  | _ => send (.fail ⟨.protocol, "Invalid parallel pair result"⟩)

/-- Compute a pure value and record it for replay. Unlike the ordinary monadic
`pure value`, this is a delayed computation with a persisted result. -/
def pure [Pure m] [Codec α] (body : Unit → α) (label : String := "") : Cloud m α :=
  send (.command inferInstance (.exec label fun _ => ExceptT.mk (Pure.pure (.ok (body ())))))

end Cloud

namespace CloudBlob

def putBytes (bytes : ByteArray) : Cloud m BlobRef :=
  Cloud.send (.command inferInstance (.putBlob bytes))
def readBytes (ref : BlobRef) : Cloud m ByteArray :=
  Cloud.send (.command inferInstance (.readBlob ref))
def resolve (name : String) : Cloud m BlobRef :=
  Cloud.send (.command inferInstance (.resolveBlob name))
def putText (text : String) : Cloud m BlobRef := putBytes text.toUTF8
def readText (ref : BlobRef) : Cloud m String := do
  let bytes ← readBytes ref
  match String.fromUTF8? bytes with
  | some text => pure text
  | none => Cloud.send (.fail ⟨.invalidUtf8, "Blob is not valid UTF-8"⟩)

/-- Resolve a blob name and read its UTF-8 text. -/
def readTextByName (name : String) : Cloud m String := do
  readText (← resolve name)

end CloudBlob

scoped infixl:30 " || " => Cloud.both

open Lean Elab Term Meta in
elab "cloud" " {" body:doSeq "}" : term <= expected => do
  let site ← SourceMap.capture (← getRef)
  withOptions (fun options => cloud.captureSource.set options true) do
    let program ← `(Cloud.delay (fun _ => do $body))
    let program ← match site with
      | none => pure program
      | some site => `(Cloud.withSource $(Syntax.mkStrLit site) $program)
    elabTerm program expected

open Lean Elab Term Meta Do Parser.Term in
private def capturingCloud : DoElabM Bool := do
  unless cloud.captureSource.get (← getOptions) do return false
  let type ← whnf (← mkMonadApp (mkConst ``Unit))
  return type.getAppFn.isConstOf ``LeanEff.EffF &&
    type.getAppArgs[0]!.getAppFn.isConstOf ``Control

open Lean Elab Term Meta Do Parser.Term in
/-- Annotate the expression before it is bound to the rest of the block. -/
@[doElem_elab Lean.Parser.Term.doExpr]
def elabCloudExpression : DoElab := fun stx dec => do
  unless ← capturingCloud do throwUnsupportedSyntax
  let `(doExpr| $expression:term) := stx | throwUnsupportedSyntax
  if let some result ← tryElabForwardApp? expression dec then return result
  let value ← elabTermEnsuringType expression (← mkMonadApp dec.resultType)
  let annotated ← match ← SourceMap.capture expression with
    | none => pure value
    | some site => mkAppM ``Cloud.withSource #[toExpr site, value, toExpr (#[] : Array (String × String))]
  dec.mkBindUnlessPure annotated

open Lean Elab Term Meta Do Parser.Term in
/-- Keep Lean's early-return behavior and annotate its resulting cloud node. -/
@[doElem_elab Lean.Parser.Term.doReturn]
def elabCloudReturn : DoElab := fun stx dec => do
  unless ← capturingCloud do throwUnsupportedSyntax
  let value ← elabDoReturn stx dec
  match ← SourceMap.capture stx with
  | none => pure value
  | some site => mkAppM ``Cloud.withSource #[toExpr site, value, toExpr (#[] : Array (String × String))]

open Lean Elab Term Meta in
/-- Distinguish helper calls before applying their optional display policy.
Supplied Cloud computations keep their own source information. -/
@[term_elab Lean.Parser.Term.app, term_elab ident]
def elabCloudFunction : TermElab := fun stx expected => do
  unless cloud.captureSource.get (← getOptions) do throwUnsupportedSyntax
  let value ← if stx.isIdent then Lean.Elab.Term.elabIdent stx expected
    else Lean.Elab.Term.elabApp stx expected
  let .const name _ := value.getAppFn | return value
  unless ← SourceMap.isCloudType (← inferType value) do return value
  let info := cloudFunc.getParam? (← getEnv) name
  let some (site, remap) ← SourceMap.functionSites name stx info | return value
  mkAppM ``Cloud.withSource #[toExpr site, value, toExpr remap]
end LeanCloud
