import LeanCloudTests.Support

namespace LeanCloudTests
open Lean LeanCloud

def roundTrips [Codec α] [BEq α] [Repr α] (name : String) (values : Array α) : TestCase :=
  ⟨s!"codec/roundtrip/{name}", do
    for value in values do
      match (Codec.decode (Codec.encode value) : Except String α) with
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
      match decodeBytes (encodeBytes bytes) with
      | .ok decoded => assertEq decoded.data bytes.data
      | .error error => throw (IO.userError error)⟩,
  ⟨"codec/roundtrip/journal", do
    for result in #[Result.suspended #[none, some (.success (toJson 7))],
        Result.completed (.failure ⟨.application, "failed"⟩), Result.completed (.success (toJson "done"))] do
      match (fromJson? (toJson result) : Except String Result) with
      | .ok decoded => assertEq decoded result
      | .error error => throw (IO.userError error)⟩,
  ⟨"codec/broken-codec-is-not-an-equivalence-case", do
    let bad : Codec Nat := ⟨"broken", fun _ => Json.null, fun _ => .error "broken codec"⟩
    let program : Program Nat := fun _ => Cloud.send (.sequential bad (.exec "value" (fun _ => pure 7)))
    let directRef ← IO.mkRef initial
    let replayRef ← IO.mkRef initial
    assertOutcome (← runDirect program directRef) (.ok 7)
    assertError (← runReplay program replayRef) .codec⟩
]

end LeanCloudTests
