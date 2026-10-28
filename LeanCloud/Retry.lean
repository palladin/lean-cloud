namespace LeanCloud.Retry

structure Failure where
  message : String
  transient : Bool := false

structure Policy where
  attempts : Nat := 3
  delayMs : Nat := 100
  maxDelayMs : Nat := 2000

/-- Retry only explicitly transient failures. Ordinary IO exceptions propagate.
The same action/request is reused; callers must tolerate a lost response after
commit. Injecting the wait makes recovery and exhaustion deterministic in tests. -/
def run (action : IO (Except Failure α)) (policy : Policy := {})
    (wait : Nat → IO Unit := fun delay => do
      IO.sleep (← IO.rand (delay / 2) delay).toUInt32) : IO α := do
  let mut delay := min policy.delayMs policy.maxDelayMs
  for attempt in [:max 1 policy.attempts] do
    match ← action with
    | .ok value => return value
    | .error failure =>
      unless failure.transient && attempt + 1 < policy.attempts do
        throw (IO.userError failure.message)
      wait delay
      delay := min policy.maxDelayMs (2 * delay)
  throw (IO.userError "Retry attempts exhausted")

/-- libcurl cancellation, certificate/URL errors and local IO failures are
permanent. DNS, connection, timeout and interrupted transfers may recover. -/
def transport (code : UInt32) : Failure := {
  message := s!"HTTP transport failed (curl {code})"
  transient := [5, 6, 7, 16, 18, 28, 35, 52, 55, 56, 92, 95].contains code.toNat }

/-- Apply the shared policy to a replay-safe HTTP operation. Application error
responses, authentication failures and malformed content are never retried. -/
def http (action : IO (Except UInt32 α)) (status : α → Nat) : IO α :=
  run do
    match ← action with
    | .error code => return .error (transport code)
    | .ok value =>
      let code := status value
      if [408, 429, 500, 502, 503, 504].contains code then
        return .error ⟨s!"HTTP {code} after transient service failure", true⟩
      return .ok value

end LeanCloud.Retry
