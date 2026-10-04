import LeanCloudCli.Effects

namespace LeanCloudCli.Native
@[extern "lc_terminal_enter"] opaque enter : IO Bool
@[extern "lc_terminal_leave"] opaque leave : IO Unit
@[extern "lc_terminal_key"] opaque key (timeoutMs : UInt32) : IO UInt32
@[extern "lc_terminal_columns"] opaque columns : IO UInt32
@[extern "lc_terminal_rows"] opaque rows : IO UInt32

private opaque LockType : NonemptyType
def Lock := LockType.type
instance : Nonempty Lock := LockType.property
@[extern "lc_scheduler_lock"] opaque lock (path : @&String) : IO Lock
@[extern "lc_scheduler_unlock"] opaque unlock (handle : @&Lock) : IO Unit

private opaque ProcessType : NonemptyType
def Process := ProcessType.type
instance : Nonempty Process := ProcessType.property
@[extern "lc_process_start"] opaque startProcess (command : @&String) (args : @&Array String) : IO Process
@[extern "lc_process_poll"] opaque pollProcess (handle : @&Process) (timeoutMs : UInt32) : IO ProcessChunk
@[extern "lc_process_close"] opaque closeProcess (handle : @&Process) : IO Unit
end LeanCloudCli.Native
