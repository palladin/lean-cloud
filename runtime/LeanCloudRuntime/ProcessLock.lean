import Lean

namespace LeanCloudRuntime.ProcessLock
private opaque HandleType : NonemptyType
def Handle := HandleType.type
instance : Nonempty Handle := HandleType.property
@[extern "lc_scheduler_lock"] opaque acquire (path : @&String) : IO Handle
@[extern "lc_scheduler_unlock"] opaque release (handle : @&Handle) : IO Unit
end LeanCloudRuntime.ProcessLock
