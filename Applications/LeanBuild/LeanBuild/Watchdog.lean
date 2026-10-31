import Std.Sync.Mutex

namespace LeanBuild

private structure WatchdogState where
  lastProgress : Nat
  generation : Nat := 0
  timedOut : Bool := false

/-- An inactivity deadline shared by completion polling and the process monitor. -/
structure Watchdog where
  private state : Std.Mutex WatchdogState
  private milliseconds : Nat
  private now : IO Nat

namespace Watchdog

def create (milliseconds : Nat) (now : IO Nat := IO.monoMsNow) : IO Watchdog := do
  return ⟨← Std.Mutex.new { lastProgress := ← now }, milliseconds, now⟩

/-- A submission after idle, a consumed completion, or the start of shutdown. -/
def progress (watchdog : Watchdog) : IO Unit := watchdog.state.atomically do
  let now ← watchdog.now
  modify fun s => { s with lastProgress := now, generation := s.generation + 1 }

def timedOut (watchdog : Watchdog) : IO Bool :=
  watchdog.state.atomically do return (← get).timedOut

/-- Filesystem probes run outside the lock. A timeout is committed only if no
progress occurred while probing, including a completion consumed by polling. -/
def check (watchdog : Watchdog) (active hasCompletion : IO Bool) : IO Bool := do
  let observed ← watchdog.state.atomically get
  if observed.timedOut then return true
  unless ← active do return false
  if (← watchdog.now) < observed.lastProgress + watchdog.milliseconds then return false
  let ready ← hasCompletion
  watchdog.state.atomically do
    let current ← get
    if current.timedOut then return true
    if current.generation != observed.generation then return false
    if ready then
      set { current with lastProgress := ← watchdog.now, generation := current.generation + 1 }
      return false
    set { current with timedOut := true }
    return true

end Watchdog
end LeanBuild
