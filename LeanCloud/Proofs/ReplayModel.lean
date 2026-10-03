import LeanCloud.Proofs.PureModel
import LeanCloud.Proofs.Model
import LeanCloud.Proofs.Db

/-! Ideal replay records and pending work. Queue selection is supplied separately. -/

namespace LeanCloud.Proofs.ReplayModel
open Lean

/-- The concrete pure backend and the abstract queue proofs share one state. -/
abbrev State := Pure.State

def db : Db State Id where
  get key state := (state.journal key, state)
  put key value state := (true, {state with journal := state.journal.write key value})

def update (state : State) (location : Location) : StepResult → State
  | .runnable locations => {state with pending := locations.toList ++ state.pending.erase location}
  | .done outcome => {state with pending := [], completed := some outcome}

def initial : State := {}

abbrev run_bind := @run_bind_state State

end LeanCloud.Proofs.ReplayModel
