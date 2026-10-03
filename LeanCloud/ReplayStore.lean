import LeanCloud.Protocol
import LeanCloud.Location

namespace LeanCloud
open Lean

/-- An immutable global replay record. Values never pass through the scheduler. -/
structure ReplayRecord where
  request : Request
  outcome : Exit
  deriving Repr, BEq, ToJson, FromJson

/-- A run-scoped namespace in global blob storage, accessed only by workers.
`create` atomically creates an absent record or returns the existing record.
The returned record is the canonical winner, even if another attempt wrote it.
A successful write is durable; reads see committed records. Transport failures
belong to `m`, so they cannot be mistaken for workflow errors. -/
structure ReplayStore (m : Type → Type u) where
  read : String → m (Option ReplayRecord)
  create : String → ReplayRecord → m ReplayRecord

namespace ReplayStore

def valueKey (location : Location) : String := location.key ++ "/value"
def returnKey (branch : Location) : String := branch.key ++ "/return"

def returnRequest : Request := ⟨"return", "exit/v1", Json.null⟩

def finish [Monad m] (store : ReplayStore m) (branch : Location) (outcome : Exit) :
    ExceptT CloudError m Unit := do
  let recorded ← store.create (returnKey branch) ⟨returnRequest, outcome⟩
  unless recorded.request == returnRequest do
    throw ⟨.divergence, "Invalid branch completion record"⟩

/-- Only clients and workers read the final value. The scheduler knows its key. -/
def outcome [Monad m] (store : ReplayStore m) (branch : Location := Location.root) :
    ExceptT CloudError m (Option Exit) := do
  let some record ← store.read (returnKey branch) | return none
  unless record.request == returnRequest do
    throw ⟨.divergence, "Invalid branch completion record"⟩
  return some record.outcome

end ReplayStore
end LeanCloud
