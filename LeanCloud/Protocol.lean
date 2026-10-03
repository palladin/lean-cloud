import Lean.Data.Json

namespace LeanCloud

open Lean
deriving instance Repr for Json

/-- A versioned, request-directed encoding. Decoding is always checked. -/
class Codec (α : Type) where
  schema : String
  encode : α → Json
  decode : Json → Except String α

@[implicit_reducible] def jsonCodec (α : Type) [ToJson α] [FromJson α] (schema : String) : Codec α :=
  ⟨schema, toJson, fromJson?⟩

instance : Codec Nat := jsonCodec Nat "nat/v1"
instance : Codec String := jsonCodec String "string/v1"
instance : Codec Bool := jsonCodec Bool "bool/v1"
instance : Codec Unit := jsonCodec Unit "unit/v1"
instance : Codec Json := ⟨"json/v1", id, .ok⟩

instance [c : Codec α] : Codec (Option α) where
  schema := s!"option({c.schema})/v1"
  encode
    | none => Json.arr #[]
    | some a => Json.arr #[c.encode a]
  decode j := do
    let xs ← j.getArr?
    match xs.toList with
    | [] => return none
    | [x] => return some (← c.decode x)
    | _ => throw "Expected zero or one option element"

instance [a : Codec α] [b : Codec β] : Codec (α × β) where
  schema := s!"pair({a.schema},{b.schema})/v1"
  encode p := Json.arr #[a.encode p.1, b.encode p.2]
  decode j := do
    let xs ← j.getArr?
    match xs.toList with
    | [x, y] => return (← a.decode x, ← b.decode y)
    | _ => throw "Expected two pair elements"

instance [c : Codec α] : Codec (Array α) where
  schema := s!"array({c.schema})/v1"
  encode xs := Json.arr (xs.map c.encode)
  decode j := do (← j.getArr?).mapM c.decode

instance [a : Codec α] [b : Codec β] : Codec (Sum α β) where
  schema := s!"sum({a.schema},{b.schema})/v1"
  encode
    | .inl value => Json.arr #[toJson "left", a.encode value]
    | .inr value => Json.arr #[toJson "right", b.encode value]
  decode j := do
    let xs ← j.getArr?
    match xs.toList with
    | [tag, value] =>
        match (← tag.getStr?) with
        | "left" => return .inl (← a.decode value)
        | "right" => return .inr (← b.decode value)
        | _ => throw "Invalid sum tag"
    | _ => throw "Expected a sum tag and value"

def encodeBytes (bytes : ByteArray) : Json :=
  toJson (bytes.data.map UInt8.toNat)

def decodeBytes (j : Json) : Except String ByteArray := do
  let values : Array Nat ← fromJson? j
  let bytes ← values.mapM fun n =>
    if n < 256 then .ok n.toUInt8 else .error "Byte outside 0..255"
  return ⟨bytes⟩

instance : Codec ByteArray := ⟨"bytes/v1", encodeBytes, decodeBytes⟩

inductive ErrorKind where
  | application | codec | divergence | missingBlob | integrity | invalidUtf8 | protocol | unsupported
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

structure CloudError where
  kind : ErrorKind := .application
  message : String
  deriving Repr, BEq, ToJson, FromJson

instance : Inhabited CloudError := ⟨⟨.protocol, ""⟩⟩

inductive Exit where
  | success (value : Json)
  | failure (error : CloudError)
  | cancelled (reason : String)
  deriving Repr, BEq, ToJson, FromJson

structure Request where
  kind : String
  schema : String
  payload : Json
  deriving Repr, ToJson, FromJson

/-- Compare the serialized request payload. Unlike Json's opaque partial
comparison, this gives the replay protocol a provably reflexive check. -/
instance : BEq Request where
  beq left right := left.kind == right.kind && left.schema == right.schema &&
    left.payload.compress == right.payload.compress

instance : ReflBEq Request where
  rfl := by intro request; simp [BEq.beq]

instance : Inhabited Request := ⟨⟨"", "", Json.null⟩⟩

/-- Deterministic FNV-1a for model corruption tests; not a cryptographic digest. -/
def modelChecksum (bytes : ByteArray) : Nat :=
  (bytes.data.foldl (fun (hash : UInt64) byte =>
    (hash ^^^ byte.toUInt64) * 1099511628211) 14695981039346656037).toNat

/-- Model references identify immutable bytes, not a worker's filesystem. -/
structure BlobRef where
  key : String
  size : Nat
  checksum : Nat
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

instance : Codec BlobRef := jsonCodec BlobRef "blob-ref/model-v1"

end LeanCloud
