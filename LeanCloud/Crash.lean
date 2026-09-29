import Lean

namespace LeanCloud

/-- Loss of a worker, not a workflow failure. Only the restart boundary handles it. -/
inductive Crash where
  | stopped
  deriving Repr, BEq, DecidableEq

/-- State survives a crash: `δ → (Except Crash α × δ)`.
Keep durable infrastructure here and worker-local state above this layer. -/
abbrev CrashM (δ : Type) := ExceptT Crash (StateM δ)

namespace CrashM

/-- Run the same attempt again after a crash, retaining its committed state.
`retries` counts additional attempts; exhaustion returns the crash and its state.
An ordinary result (including `Except.error CloudError`) is returned immediately.

For the replay interpreter, pass `(interpret ...).run freshLocalState` as the
attempt. Every retry starts with that local state; no continuation is retained.
The caller initializes durable state once, before entering this runner. -/
def restart (retries : Nat) (attempt : CrashM δ α) : CrashM δ α := fun durable =>
  match attempt.run durable with
  | (.ok value, durable') => (.ok value, durable')
  | (.error crash, durable') =>
    match retries with
    | 0 => (.error crash, durable')
    | retries + 1 => (restart retries attempt).run durable'

end CrashM
end LeanCloud
