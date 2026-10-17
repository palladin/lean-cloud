namespace LeanCloudRuntime.Digest

@[extern "lean_cloud_sha256_bytes"]
opaque bytes (value : @& ByteArray) : IO String

@[extern "lean_cloud_sha256_file"]
opaque file (path : @& String) : IO String

/-- Copy and hash a bounded range from an immutable pack into a private file. -/
@[extern "lean_cloud_copy_range"]
opaque copyRange (source destination : @& String) (offset length : UInt64)
    (executable : Bool := false) : IO String

end LeanCloudRuntime.Digest
