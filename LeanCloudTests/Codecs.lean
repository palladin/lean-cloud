import LeanCloudTests.Support

namespace LeanCloudTests
open Lean LeanCloud

def roundTrips [Codec α] [BEq α] [Repr α] (name : String) (values : Array α) : TestCase :=
  ⟨s!"codec/roundtrip/{name}", do
    for value in values do
      match (Json.parse (Codec.encode value).compress >>= Codec.decode : Except String α) with
      | .ok decoded => assertEq decoded value
      | .error error => throw (IO.userError error)⟩

def rejects (α : Type) [Codec α] (name : String) (values : Array Json) : TestCase :=
  ⟨s!"codec/reject/{name}", do
    for value in values do
      match (Codec.decode value : Except String α) with
      | .ok _ => throw (IO.userError s!"Accepted malformed value: {value}")
      | .error _ => pure ()⟩

def codecCases : Array TestCase := #[
  roundTrips "nat" #[0, 1, 255, 65536, 2^128 + 17],
  roundTrips "string" #["", "plain", "λ 🌍\n\u0000"],
  roundTrips "bool" #[false, true],
  roundTrips "unit" #[()],
  roundTrips "option" #[(none : Option Nat), some 0, some (2^80)],
  roundTrips "nested-option" #[(none : Option (Option Nat)), some none, some (some 5)],
  roundTrips "array" #[(#[] : Array Nat), #[1], #[0, 2^100, 9]],
  roundTrips "pair" #[((0 : Nat), ""), (7, "seven")],
  roundTrips "sum" #[(Sum.inl 7 : Sum Nat String), .inr "text"],
  roundTrips "blob-ref" #[makeRef "empty" "".toUTF8, makeRef "unicode" "λ".toUTF8],
  rejects Nat "nat" #[Json.str "wrong", Json.arr #[]],
  rejects (Option Nat) "option" #[Json.arr #[toJson 1, toJson 2], Json.null],
  rejects (Nat × String) "pair" #[Json.arr #[], Json.arr #[toJson 1], Json.arr #[toJson 1, toJson "a", toJson 3]],
  rejects (Sum Nat String) "sum" #[Json.arr #[toJson "unknown", toJson 1], Json.arr #[]],
  rejects ByteArray "bytes" #[toJson (#[256] : Array Nat), Json.str "bytes"],
  ⟨"codec/roundtrip/bytes", do
    for bytes in #[ByteArray.empty, ByteArray.mk ((List.range 256).toArray.map Nat.toUInt8)] do
      match Json.parse (encodeBytes bytes).compress >>= decodeBytes with
      | .ok decoded => assertEq decoded.data bytes.data
      | .error error => throw (IO.userError error)⟩,
  ⟨"codec/roundtrip/replay-record", do
    let record : ReplayRecord := ⟨ReplayStore.returnRequest, .success (toJson (7 : Nat))⟩
    let decoded ← unwrap (Json.parse (toJson record).compress >>= fromJson? (α := ReplayRecord))
    assertEq decoded record⟩,
  ⟨"protocol/request-check-survives-persistence", do
    -- These are every payload shape emitted by replay's request signatures.
    let payloads := #[Json.null, toJson "λ 🌍\n\u0000", toJson (2^128 : Nat),
      encodeBytes (ByteArray.mk ((List.range 256).toArray.map Nat.toUInt8)),
      toJson (makeRef "λ/ref" "content".toUTF8)]
    for payload in payloads do
      let request : Request := ⟨"operation", "schema/v1", payload⟩
      let decoded ← unwrap (Json.parse (toJson request).compress >>= fromJson? (α := Request))
      assertTrue (decoded == request) "Persisted request no longer matches"
      assertTrue (decoded != { request with kind := "other" }) "Changed operation was accepted"
      assertTrue (decoded != { request with schema := "schema/v2" }) "Changed codec was accepted"
      assertTrue (decoded != { request with payload := Json.str "changed" }) "Changed input was accepted"⟩
]

end LeanCloudTests
