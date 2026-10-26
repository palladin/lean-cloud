namespace LeanCloudRuntime.Digest

@[extern "lean_cloud_sha256_bytes"]
opaque bytes (value : @& ByteArray) : IO String

/-- Native SHA-256 and the existing reference checksum, without converting
every byte into a Lean array element. Keeps existing BlobRef encodings valid. -/
@[extern "lean_cloud_blob_fingerprint"]
opaque fingerprint (value : @& ByteArray) : IO (String × Nat)

private opaque StateType : NonemptyType
def State := StateType.type
instance : Nonempty State := StateType.property

/-- A streaming digest owned by one sequential caller. -/
@[extern "lean_cloud_sha256_new"] opaque start : IO State
@[extern "lean_cloud_sha256_update"] opaque update (state : @&State) (bytes : @&ByteArray) : IO Unit
@[extern "lean_cloud_sha256_finish"] opaque finish (state : @&State) : IO String

@[extern "lean_cloud_sha256_file"]
opaque file (path : @& String) : IO String

/-- Copy and hash a bounded range from an immutable pack into a private file. -/
@[extern "lean_cloud_copy_range"]
opaque copyRange (source destination : @& String) (offset length : UInt64)
    (executable : Bool := false) : IO String

end LeanCloudRuntime.Digest
