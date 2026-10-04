import LeanCloud.Control
import LeanCloud.SourceMap
import Lean.Elab.BuiltinDo

universe u

namespace LeanCloud
open Lean LeanEff

/-- The cloud monad uses lean-eff's shared core with one higher-order effect family. -/
abbrev Cloud (m : Type → Type u) := EffF (Control m) SourceSiteId

variable {m : Type → Type u}

namespace Cloud

mutual
  /-- Supply a call site to unannotated nodes, including higher-order children.
  Inner cloud blocks retain their own sites. Continuations stay delayed. -/
  def withSource {m : Type → Type u} {α : Type} (site : SourceSiteId) (program : Cloud m α) : Cloud m α :=
    match program with
    | .pure info value => .pure (info.orElse (fun _ => some site)) value
    | .impure info request next => .impure (info.orElse (fun _ => some site))
        (sourceControl site request) (sourceContinuation site next)
  termination_by structural program

  def sourceControl {m : Type → Type u} {α : Type} (site : SourceSiteId) (request : Control m α) : Control m α :=
    match request with
    | .parallel codec count branches => .parallel codec count fun i => withSource site (branches i)
    | other => other
  termination_by structural request

  def sourceContinuation {m : Type → Type u} {α β : Type} (site : SourceSiteId)
      (next : ArrsF (Control m) SourceSiteId α β) : ArrsF (Control m) SourceSiteId α β :=
    match next with
    | .one k => .one fun value => withSource site (k value)
    | .append first rest => .append (sourceContinuation site first) (sourceContinuation site rest)
  termination_by structural next
end

def send (request : Control m α) : Cloud m α := EffF.send request

def delay (body : Unit → Cloud m α) : Cloud m α := send Control.delay >>= body

def fail (message : String) : Cloud m α := send (.fail ⟨.application, message⟩)

def decode [Codec α] (value : Json) : Cloud m α :=
  match Codec.decode value with
  | .ok value => pure value
  | .error error => send (.fail ⟨.codec, error⟩)

def exec [Codec α] (body : Unit → m α) (label : String := "") : Cloud m α :=
  send (.command inferInstance (.exec label body))

def parallel [Codec α] (branches : Array (Cloud m α)) : Cloud m (Array α) :=
  send (.parallel inferInstance branches.size (fun index => branches[index]))

/-- Heterogeneous pairing uses the same collection-parallel primitive. -/
def both [Codec α] [Codec β] (left : Cloud m α) (right : Cloud m β) : Cloud m (α × β) := do
  let values ← parallel #[Sum.inl <$> left, Sum.inr <$> right]
  match values.toList with
  | [.inl a, .inr b] => return (a, b)
  | _ => send (.fail ⟨.protocol, "Invalid parallel pair result"⟩)

/-- Compute a pure value and record it for replay. Unlike the ordinary monadic
`pure value`, this is a delayed computation with a persisted result. -/
def pure [Pure m] [Codec α] (body : Unit → α) (label : String := "") : Cloud m α :=
  exec (fun _ => Pure.pure (body ())) label

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
    | some site => mkAppM ``Cloud.withSource #[toExpr site, value]
  dec.mkBindUnlessPure annotated

open Lean Elab Term Meta Do Parser.Term in
/-- Keep Lean's early-return behavior and annotate its resulting cloud node. -/
@[doElem_elab Lean.Parser.Term.doReturn]
def elabCloudReturn : DoElab := fun stx dec => do
  unless ← capturingCloud do throwUnsupportedSyntax
  let value ← elabDoReturn stx dec
  match ← SourceMap.capture stx with
  | none => pure value
  | some site => mkAppM ``Cloud.withSource #[toExpr site, value]

end LeanCloud
