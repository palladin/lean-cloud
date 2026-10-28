import LeanCloud.Retry
import LeanCloudTests.Support

namespace LeanCloudTests.Retry
open LeanCloud

def cases : Array TestCase := #[
  ⟨"retry.transient-backoff-and-success", do
    let calls ← IO.mkRef 0
    let waits ← IO.mkRef (#[] : Array Nat)
    let value ← Retry.run (do
      calls.modify (· + 1)
      if (← calls.get) < 3 then return .error (Retry.transport 28)
      return .ok (42 : Nat)) {} (fun delay => waits.modify (·.push delay))
    assertEq value 42
    assertEq (← calls.get) 3
    assertEq (← waits.get) #[100, 200]⟩,
  ⟨"retry.exhaustion-permanent-errors-and-cancellation", do
    for code in #[6, 28, 42, 60] do
      let calls ← IO.mkRef 0
      let failed ← try
        discard <| Retry.run (α := Unit) (do
          calls.modify (· + 1)
          return .error (Retry.transport code)) {} (fun _ => pure ())
        pure false
      catch _ => pure true
      assertTrue failed "Retry swallowed a failure"
      assertEq (← calls.get) (if code == 6 || code == 28 then 3 else 1)
    let calls ← IO.mkRef 0
    try
      discard <| Retry.run (α := Unit) (do
        calls.modify (· + 1)
        throw (IO.userError "application failure"))
    catch _ => pure ()
    assertEq (← calls.get) 1 "Application exception was retried"⟩ ]

end LeanCloudTests.Retry
