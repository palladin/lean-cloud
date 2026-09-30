import LeanCloud.ReplayInterpreter

/-! One iteration of the actual replay loop, including polling and publication.
ConcurrentIteration proves its correspondence with the public loop. -/

namespace LeanCloud.Proofs.ReplayIteration
open Lean ReplayInterpreter.Internal

universe u

/-- Proof view of one loop iteration. `none` continues the loop; `some` returns
the observed completion. This uses the actual worker and queue operations. -/
def iteration {m : Type → Type u} [Monad m] (db : Db σ m) (blobs : BlobStorage σ m)
    (queue : WorkQueue σ m) (fuel : Nat) (source : Cloud m Json) :
    ExceptT CloudError (StateT σ m) (Option Exit) := do
  match ← queue.next with
  | .idle => pure none
  | .completed outcome => pure (some outcome)
  | .item location =>
    let response ← step db blobs fuel source location
    queue.complete location response
    pure (match response with | .done outcome => some outcome | .runnable _ => none)

end LeanCloud.Proofs.ReplayIteration
