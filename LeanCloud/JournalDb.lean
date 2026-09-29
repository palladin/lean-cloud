import LeanCloud.Db
import LeanCloud.Result

/-! Physical journal layout for immutable outcomes. The interpreter sees a
logical `Result`; a partial group's array is assembled from independent records.
All workers of a run must use this adapter over the same run-scoped raw Db.
The layout is distinct from the ideal logical-map backend used in the existing
serialized equivalence proof; no automatic storage refinement is assumed. -/

namespace LeanCloud.JournalDb
open Lean

def resultKey (key : String) : String := key ++ "/result"
def forkKey (key : String) : String := key ++ "/fork"
def childKey (key : String) (index : Nat) : String := key ++ "/child/" ++ toString index

/-- Repeated writes of the same value are harmless; observed disagreements are
rejected. With only atomic get/put, the check is not compare-and-set: overlapping
writers to the SAME key must agree on its value (as in a stable pure workflow).
Arbitrary duplicate IO executions are not made exactly-once by this adapter. -/
def putSame [Monad m] (db : Db σ m) (key : String) (value : Json) : StateT σ m Bool := do
  match ← db.get key with
  | none => db.put key value
  | some existing => return existing == value

/-- Errors in the physical format become malformed logical records, which the
interpreter reports through its existing CloudError codec channel. -/
private def malformed (message : String) : Option Json := some (Json.str message)

def get [Monad m] (db : Db σ m) (key : String) : StateT σ m (Option Json) := do
  if let some value ← db.get (resultKey key) then
    match fromJson? (α := Exit) value with
    | .ok outcome => return some (toJson (Result.completed outcome))
    | .error error => return malformed s!"Invalid result: {error}"
  let some descriptor ← db.get (forkKey key) | return none
  let count ← match fromJson? (α := Nat) descriptor with
    | .ok count => pure count
    | .error error => return malformed s!"Invalid fork: {error}"
  let mut children := #[]
  for index in [:count] do
    match ← db.get (childKey key index) with
    | none => children := children.push none
    | some value =>
      match fromJson? (α := Exit) value with
      | .ok outcome => children := children.push (some outcome)
      | .error error => return malformed s!"Invalid child result: {error}"
  return some (toJson (Result.settle children))

/-- A partial snapshot writes only present slots. Missing slots NEVER erase a
record. Fork descriptors, child outcomes, and completed results have different
keys, so stale fork initialization cannot overwrite a completed group. -/
def put [Monad m] (db : Db σ m) (key : String) (value : Json) : StateT σ m Bool := do
  let result ← match fromJson? (α := Result) value with
    | .ok result => pure result
    | .error _ => return false
  match result with
  | .completed outcome => putSame db (resultKey key) (toJson outcome)
  | .suspended children =>
    unless ← putSame db (forkKey key) (toJson children.size) do return false
    for index in [:children.size] do
      if let some outcome := children[index]! then
        unless ← putSame db (childKey key index) (toJson outcome) do return false
    return true

def ofDb [Monad m] (db : Db σ m) : Db σ m where
  get := get db
  put := put db

end LeanCloud.JournalDb
