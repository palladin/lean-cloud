import LeanCloud.Control

universe u

namespace LeanCloud
open Lean LeanEff

/-- The cloud monad uses lean-eff's shared core with one higher-order effect family. -/
abbrev Cloud (m : Type → Type u) := EffF (Control m)

variable {m : Type → Type u}

namespace Cloud

def send (request : Control m α) : Cloud m α := EffF.send request

def delay (body : Unit → Cloud m α) : Cloud m α := send Control.delay >>= body

def fail (message : String) : Cloud m α := send (.fail ⟨.application, message⟩)

def decode [Codec α] (value : Json) : Cloud m α :=
  match Codec.decode value with
  | .ok value => pure value
  | .error error => send (.fail ⟨.codec, error⟩)

def exec [Codec α] (body : Unit → m α) (label : String := "") : Cloud m α :=
  send (.sequential inferInstance (.exec label body))

def parallel [Codec α] (branches : Array (Cloud m α)) : Cloud m (Array α) :=
  send (.parallel inferInstance branches.size (fun index => branches[index]))

/-- Reserved for choice semantics; both current interpreters return `unsupported`. -/
def choice [Codec α] (branches : Array (Cloud m (Option α))) : Cloud m (Option α) :=
  send (.choice inferInstance branches.size (fun index => branches[index]))

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
  Cloud.send (.sequential inferInstance (.putBlob bytes))
def readBytes (ref : BlobRef) : Cloud m ByteArray :=
  Cloud.send (.sequential inferInstance (.readBlob ref))
def resolve (name : String) : Cloud m BlobRef :=
  Cloud.send (.sequential inferInstance (.resolveBlob name))
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
syntax "cloud" " {" doSeq "}" : term
macro_rules
  | `(cloud { $body:doSeq }) => `(Cloud.delay (fun _ => do $body))

end LeanCloud
