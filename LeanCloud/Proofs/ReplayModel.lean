import LeanCloud.ReplayInterpreter
import LeanCloud.Proofs.Model
import LeanCloud.Proofs.Db

/-! Ideal replay records and pending work. Queue selection is supplied separately. -/

namespace LeanCloud.Proofs.ReplayModel
open Lean

structure State where
  journal : Journal := Journal.empty
  pending : List Location := [Location.root]
  completed : Option Exit := none

def db : Db State Id where
  get key state := (state.journal key, state)
  put key value state := (true, {state with journal := state.journal.write key value})

def update (state : State) (location : Location) : StepResult → State
  | .runnable locations => {state with pending := locations.toList ++ state.pending.erase location}
  | .done outcome => {state with pending := [], completed := some outcome}

def initial : State := {}

abbrev run_bind := @run_bind_state State

end LeanCloud.Proofs.ReplayModel
