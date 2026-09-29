import LeanCloud.Crash

/-! Fault injection around atomic backend operations. This models one worker
attempt at a time. It imposes no transaction across multiple operations. -/

namespace LeanCloud.CrashModel

inductive Boundary where
  | before
  | after
  deriving Repr, BEq, DecidableEq

/-- Harness bookkeeping, not application data or part of the durable backend.
One entry is consumed per primitive invocation. An exhausted script allows all
subsequent invocations to succeed; retries do not reset the script. -/
structure Faults where
  script : List (Option Boundary) := []
  calls : Nat := 0
  deriving Repr, BEq

structure State (δ : Type) where
  durable : δ
  faults : Faults := {}

abbrev M (δ : Type) := CrashM (State δ)

/-- Commit the whole transition or none of it. A crash after the commit preserves
the new durable state but prevents the worker from receiving the return value. -/
def atomic (operation : δ → α × δ) : M δ α := fun state =>
  let boundary := state.faults.script.headD none
  let faults := { script := state.faults.script.drop 1, calls := state.faults.calls + 1 : Faults }
  match boundary with
  | some .before => (.error .stopped, { state with faults })
  | _ =>
    let (value, durable) := operation state.durable
    let result := if boundary == some .after then .error .stopped else .ok value
    (result, { durable, faults })

end LeanCloud.CrashModel
