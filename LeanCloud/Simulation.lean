import LeanEff.Core

/-! External scheduling of atomic backend calls. Continuations are volatile:
pausing retains them, crashing discards them, and restart creates a fresh attempt.
This is a model of worker execution, not an additional Cloud control effect. -/

namespace LeanCloud

inductive Atomic (δ : Type) : Type → Type where
  | step {α : Type} : (δ → α × δ) → Atomic δ α

abbrev SimM (δ : Type) := LeanEff.EffF (Atomic δ)

def SimM.atomic (operation : δ → α × δ) : SimM δ α :=
  LeanEff.EffF.send (.step operation)

namespace Simulation
open LeanEff

inductive Phase where
  | waiting | responding | stopped | finished
  deriving Repr, BEq, DecidableEq

/-- A reply is saved separately from its continuation so another worker can run,
or this worker can crash, after commit and before receiving the response. -/
inductive Worker (δ α : Type) where
  | waiting {β : Type} (operation : δ → β × δ) (next : ArrsF (Atomic δ) β α)
  | responding {β : Type} (value : β) (next : ArrsF (Atomic δ) β α)
  | stopped
  | finished (value : α)

def Worker.ofProgram : SimM δ α → Worker δ α
  | .pure value => .finished value
  | .impure (.step operation) next => .waiting operation next

def Worker.phase : Worker δ α → Phase
  | .waiting .. => .waiting
  | .responding .. => .responding
  | .stopped => .stopped
  | .finished .. => .finished

def Worker.outcome? : Worker δ α → Option α
  | .finished value => some value
  | _ => none

structure State (δ α : Type) (count : Nat) where
  durable : δ
  workers : Fin count → Worker δ α

def State.initial (durable : δ) (start : Fin count → SimM δ α) : State δ α count :=
  ⟨durable, fun worker => .ofProgram (start worker)⟩

def State.setWorker (state : State δ α count) (worker : Fin count)
    (next : Worker δ α) : State δ α count :=
  { state with workers := fun index => if index = worker then next else state.workers index }

inductive Event (count : Nat) where
  | commit (worker : Fin count)
  | resume (worker : Fin count)
  | crash (worker : Fin count)
  | restart (worker : Fin count)
  | advanceTime (elapsed : Nat)
  deriving Repr, BEq, DecidableEq

inductive Error where
  | notWaiting | notResponding | notRunning | notStopped
  deriving Repr, BEq, DecidableEq

/-- Exactly one external event. Only commit and explicit time advancement can
change shared state. Pure continuation evaluation runs up to the next request.
An invalid schedule is rejected rather than silently treated as progress. -/
def step (start : Fin count → SimM δ α) (advance : Nat → δ → δ)
    (event : Event count) (state : State δ α count) : Except Error (State δ α count) :=
  match event with
  | .commit worker =>
    match state.workers worker with
    | .waiting operation next =>
      let (value, durable) := operation state.durable
      .ok { state.setWorker worker (.responding value next) with durable }
    | _ => .error .notWaiting
  | .resume worker =>
    match state.workers worker with
    | .responding value next =>
      .ok (state.setWorker worker (.ofProgram (ArrsF.apply next value)))
    | _ => .error .notResponding
  | .crash worker =>
    match state.workers worker with
    | .waiting .. | .responding .. => .ok (state.setWorker worker .stopped)
    | _ => .error .notRunning
  | .restart worker =>
    match state.workers worker with
    | .stopped => .ok (state.setWorker worker (.ofProgram (start worker)))
    | _ => .error .notStopped
  | .advanceTime elapsed => .ok { state with durable := advance elapsed state.durable }

/-- A finite reproducible schedule. Script exhaustion leaves the machine paused;
it is neither workflow completion nor a CloudError. -/
def run (start : Fin count → SimM δ α) (advance : Nat → δ → δ)
    (events : List (Event count)) (state : State δ α count) : Except Error (State δ α count) :=
  events.foldlM (fun state event => step start advance event state) state

end Simulation
end LeanCloud
