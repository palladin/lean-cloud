import LeanCloud.Backend.Model

/-! Executable checking of sequential primitive observations against the common
model. Ambiguous queue deliveries retain every possible publication identity.
This checker is test support, not a proof of an external service. Concurrent
invocation/response histories additionally require a linearization search. -/

namespace LeanCloud.Backend.Check

private def same (operation : Request α) (left right : α) : Bool :=
  match operation with
  | .get _ => left == right
  | .put .. => left == right
  | .enqueue _ => true
  | .dequeue => left == right
  | .acknowledge _ => left == right

private def choices (operation : Request α) (state : State) : Array Decision :=
  match operation with
  | .dequeue => #[{}] ++ (Array.range state.queue.messages.size).map fun id => ⟨some id, true⟩
  | .acknowledge _ => #[⟨none, false⟩, ⟨none, true⟩]
  | _ => #[{}]

def candidates (operation : Request α) (reply : α) (state : State) : Array State :=
  (choices operation state).filterMap fun decision =>
    match execute decision operation state with
    | .ok (expected, after) => if same operation reply expected then some after else none
    | .error _ => none

/-- Apply one successful observation. Put rejection is deliberately excluded
from this generator's compatible-write scenarios; infrastructure exceptions
and concurrent operation intervals need the separate request history model. -/
def observe (operation : Request α) (reply : α) (possible : Array State) : Except String (Array State) :=
  let next := possible.foldl (fun states before => states ++ candidates operation reply before) #[]
  if next.isEmpty then .error "Backend observation violates the primitive model"
  else .ok next

end LeanCloud.Backend.Check
