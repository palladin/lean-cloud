import LeanCloud.Proofs.Assumptions
import LeanCloud.ReplayInterpreter
import Init.Data.Array.Monadic

/-! Round-trip laws for the codecs and journal records used by replay. -/

namespace LeanCloud.Proofs
open Lean

theorem codec_encode_injective (codec : Codec α) (law : CodecLaw codec)
    {a b : α} (equal : codec.encode a = codec.encode b) : a = b := by
  have decoded := congrArg codec.decode equal
  rw [law a, law b] at decoded
  exact Except.ok.inj decoded

theorem codec_json : CodecLaw (inferInstance : Codec Json) := fun _ => rfl
theorem codec_nat : CodecLaw (inferInstance : Codec Nat) := fun _ => rfl
theorem codec_string : CodecLaw (inferInstance : Codec String) := fun _ => rfl
theorem codec_bool : CodecLaw (inferInstance : Codec Bool) := fun _ => rfl
theorem codec_unit : CodecLaw (inferInstance : Codec Unit) := by
  intro value
  cases value
  rfl

theorem codec_option [codec : Codec α] (law : CodecLaw codec) :
    CodecLaw (inferInstance : Codec (Option α)) := by
  intro value
  cases value with
  | none => rfl
  | some value =>
    change (do let decoded ← codec.decode (codec.encode value); pure (some decoded)) = _
    rw [law]
    rfl

theorem codec_pair [a : Codec α] [b : Codec β] (lawA : CodecLaw a) (lawB : CodecLaw b) :
    CodecLaw (inferInstance : Codec (α × β)) := by
  intro value
  change (do
    let first ← a.decode (a.encode value.1)
    let second ← b.decode (b.encode value.2)
    pure (first, second)) = _
  rw [lawA, lawB]
  rfl

theorem codec_array [codec : Codec α] (law : CodecLaw codec) :
    CodecLaw (inferInstance : Codec (Array α)) := by
  intro values
  change (values.map codec.encode).mapM codec.decode = .ok values
  change ∀ value, codec.decode (codec.encode value) = .ok value at law
  simp only [Array.mapM_map, Function.comp_def, law]
  simpa [pure, Except.pure] using (Array.mapM_pure (m := Except String) (xs := values) (f := id))

theorem codec_sum [a : Codec α] [b : Codec β] (lawA : CodecLaw a) (lawB : CodecLaw b) :
    CodecLaw (inferInstance : Codec (Sum α β)) := by
  intro value
  cases value with
  | inl value =>
    change (do let decoded ← a.decode (a.encode value); pure (Sum.inl decoded)) = _
    rw [lawA]
    rfl
  | inr value =>
    change (do let decoded ← b.decode (b.encode value); pure (Sum.inr decoded)) = _
    rw [lawB]
    rfl

private theorem json_array_roundtrip [ToJson α] [FromJson α]
    (law : ∀ value : α, fromJson? (toJson value) = .ok value) (values : Array α) :
    fromJson? (toJson values) = .ok values := by
  change (values.map toJson).mapM fromJson? = .ok values
  simp only [Array.mapM_map, Function.comp_def, law]
  simpa [pure, Except.pure] using (Array.mapM_pure (m := Except String) (xs := values) (f := id))

theorem codec_bytes : CodecLaw (inferInstance : Codec ByteArray) := by
  intro bytes
  rcases bytes with ⟨data⟩
  change decodeBytes (encodeBytes ⟨data⟩) = .ok ⟨data⟩
  unfold decodeBytes encodeBytes
  rw [json_array_roundtrip (α := Nat) (fun _ => rfl)]
  change (do
    let bytes ← (data.map UInt8.toNat).mapM (fun n =>
      if n < 256 then (Except.ok n.toUInt8 : Except String UInt8)
      else .error "Byte outside 0..255")
    pure ({ data := bytes } : ByteArray)) = .ok { data := data }
  rw [Array.mapM_map]
  have byte_decode : (fun byte : UInt8 =>
      if byte.toNat < 256 then (Except.ok byte.toNat.toUInt8 : Except String UInt8)
      else .error "Byte outside 0..255") = fun byte => .ok byte := by
    funext byte
    have bound : byte.toNat < 256 := UInt8.toNat_lt byte
    simp [bound, Nat.toUInt8]
  simp only [Function.comp_def]
  rw [byte_decode]
  have traverse : data.mapM (fun byte => (Except.ok byte : Except String UInt8)) = .ok data := by
    simpa [pure, Except.pure] using (Array.mapM_pure (m := Except String) (xs := data) (f := id))
  rw [traverse]
  rfl

theorem errorKind_roundtrip (kind : ErrorKind) : fromJson? (toJson kind) = .ok kind := by
  cases kind <;> rfl

theorem cloudError_roundtrip (error : CloudError) : fromJson? (toJson error) = .ok error := by
  rcases error with ⟨kind, message⟩
  cases kind <;> rfl

theorem codec_blobRef : CodecLaw (inferInstance : Codec BlobRef) := by
  intro ref
  cases ref
  rfl

private theorem tag_singleton (tag : String) (value : Json) :
    (Json.mkObj [(tag, value)]).getTag? = some tag := by
  change (guard (true = true) *>
    Std.DTreeMap.Internal.Impl.minKey? (β := fun _ : String => Json)
      (.inner 1 tag value .leaf .leaf) : Option String) = _
  simp [Std.DTreeMap.Internal.Impl.minKey?, guard]
  rfl

theorem exit_roundtrip (outcome : Exit) : fromJson? (toJson outcome) = .ok outcome := by
  cases outcome with
  | success value =>
    simp [fromJson?, toJson, instFromJsonExit.fromJson, instToJsonExit.toJson,
      tag_singleton, Json.parseCtorFields]
    rfl
  | failure error =>
    simp [fromJson?, toJson, instFromJsonExit.fromJson, instToJsonExit.toJson,
      tag_singleton, Json.parseCtorFields]
    change (Exit.failure <$> fromJson? (toJson error)) = _
    rw [cloudError_roundtrip]
    rfl
  | cancelled reason =>
    simp [fromJson?, toJson, instFromJsonExit.fromJson, instToJsonExit.toJson,
      tag_singleton, Json.parseCtorFields]
    rfl

private theorem optional_exit_roundtrip (outcome : Option Exit) :
    fromJson? (toJson outcome) = .ok outcome := by
  cases outcome with
  | none => rfl
  | some outcome =>
    have decode : fromJson? (toJson (some outcome)) = some <$> (fromJson? (toJson outcome) : Except String Exit) := by
      cases outcome <;> rfl
    rw [decode, exit_roundtrip]
    rfl

/-- The actual derived serializer for persisted results round-trips both completed
outcomes and partially filled parallel groups. -/
theorem result_roundtrip (result : Result) : fromJson? (toJson result) = .ok result := by
  cases result with
  | completed outcome =>
    simp [fromJson?, toJson, instFromJsonResult.fromJson, instToJsonResult.toJson,
      tag_singleton, Json.parseCtorFields]
    change (Result.completed <$> fromJson? (toJson outcome)) = _
    rw [exit_roundtrip]
    rfl
  | suspended children =>
    simp [fromJson?, toJson, instFromJsonResult.fromJson, instToJsonResult.toJson,
      tag_singleton, Json.parseCtorFields]
    change (Result.suspended <$> (children.map toJson).mapM (fromJson? (α := Option Exit))) = _
    simp only [Array.mapM_map, Function.comp_def, optional_exit_roundtrip]
    have traverse : children.mapM (fun value => (Except.ok value : Except String (Option Exit))) =
        .ok children := by
      simpa [pure, Except.pure] using (Array.mapM_pure (m := Except String) (xs := children) (f := id))
    rw [traverse]
    rfl

end LeanCloud.Proofs
