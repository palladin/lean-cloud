import LeanCloudTests.Support

/-! Single-worker drivers for the same external simulation used by concurrent tests.
The driver budget limits test execution; exhausting it does not crash a workflow. -/
namespace LeanCloudTests.SimTest
open LeanCloud Simulation

abbrev Machine (δ α : Type) := Simulation.State δ α 1

def events (action : SimM δ α) (advance : Nat → δ → δ)
    (schedule : List (Event 1)) (state : Machine δ α) : Except String (Machine δ α) :=
  (Simulation.run (fun _ => action) advance schedule state).mapError reprStr

def initial (action : SimM δ α) (durable : δ) : Machine δ α :=
  Simulation.State.initial durable (fun _ => action)

def nextEvent (state : Machine δ α) : Option (Event 1) :=
  match (state.workers 0).phase with
  | .waiting => some (.commit 0)
  | .responding => some (.resume 0)
  | .stopped => some (.restart 0)
  | .finished => none

def run (budget : Nat) (action : SimM δ α) (state : Machine δ α)
    (advance : Nat → δ → δ := fun _ s => s) (elapsed : Nat := 0) :
    Except String (Machine δ α) := do
  let some event := nextEvent state | return state
  match budget with
  | 0 => throw "Simulation event budget exhausted"
  | budget + 1 =>
    let schedule := if elapsed == 0 then [event] else [.advanceTime elapsed, event]
    run budget action (← events action advance schedule state) advance elapsed

def value (state : Machine δ α) : IO α :=
  match (state.workers 0).outcome? with
  | some value => pure value
  | none => throw (IO.userError "Worker has not finished")

def finish (action : SimM δ α) (durable : δ)
    (advance : Nat → δ → δ := fun _ s => s) (elapsed : Nat := 0)
    (budget : Nat := 30000) : IO (α × δ) := do
  let .ok final := run budget action (initial action durable) advance elapsed
    | throw (IO.userError "Simulation did not finish")
  return (← value final, final.durable)

/-- Every waiting and responding boundary of an uninterrupted execution. -/
def prefixes (budget : Nat) (action : SimM δ α) (state : Machine δ α) :
    Except String (List (Machine δ α)) := do
  let some event := nextEvent state | return []
  match budget with
  | 0 => throw "Prefix enumeration budget exhausted"
  | budget + 1 =>
    return state :: (← prefixes budget action (← events action (fun _ s => s) [event] state))

end LeanCloudTests.SimTest
