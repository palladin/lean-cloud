import LeanCloud.JournalDb

namespace LeanCloud.CompletionStore
open Lean

/-- Run-scoped physical key shared by workers and backend models. -/
def key : String := "completed"

def read [Monad m] (db : Db σ m) (invalid : String → m (Option Exit)) :
    StateT σ m (Option Exit) := do
  let some value ← db.get key | return none
  match fromJson? value with
  | .ok outcome => return some outcome
  | .error _ => liftM (invalid "Invalid workflow completion record")

def write [Monad m] (db : Db σ m) (invalid : String → m Unit)
    (outcome : Exit) : StateT σ m Unit := do
  unless ← JournalDb.putSame db key (toJson outcome) do
    liftM (invalid "Db rejected workflow completion record")

end LeanCloud.CompletionStore
