import LeanEff.Core

/-! Atomic effects expose scheduling boundaries without changing the interpreter.
Local operations die with their process. Remote requests may still commit after a
crash; their abandoned continuations never run. Commit and reply are separate. -/

namespace LeanCloud

inductive Atomic (δ : Type) : Type → Type where
  | step {α : Type} (remote : Bool) (label : String) (operation : δ → α × δ) : Atomic δ α

abbrev SimM (δ : Type) := LeanEff.EffF (Atomic δ) Empty

def SimM.atomic (operation : δ → α × δ) (label : String := "remote") : SimM δ α :=
  LeanEff.EffF.send (.step true label operation)

def SimM.local (operation : δ → α × δ) (label : String := "local") : SimM δ α :=
  LeanEff.EffF.send (.step false label operation)

namespace Simulation
open LeanEff

inductive Actor (δ α : Type) where
  | waiting {β : Type} (remote : Bool) (label : String)
      (operation : δ → β × δ) (next : ArrsF (Atomic δ) Empty β α)
  | responding {β : Type} (value : β) (next : ArrsF (Atomic δ) Empty β α)
  | stopped
  | finished (value : α)

def Actor.ofProgram : SimM δ α → Actor δ α
  | .pure _ value => .finished value
  | .impure _ (.step remote label operation) next => .waiting remote label operation next

structure Orphan (δ : Type) where
  label : String
  commit : δ → δ

structure State (δ α : Type) (count : Nat) where
  world : δ
  actors : Fin count → Actor δ α
  generations : Fin count → Nat := fun _ => 0
  orphans : Array (Orphan δ) := #[]

/-- Generation distinguishes process attempts and consumer sessions. Scheduler
restart replaces its continuation; its private durable database survives. -/
abbrev Start (δ α : Type) (count : Nat) := Fin count → Nat → SimM δ α

def State.initial (world : δ) (start : Start δ α count) : State δ α count :=
  ⟨world, fun actor => .ofProgram (start actor 0), fun _ => 0, #[]⟩

def State.setActor (state : State δ α count) (actor : Fin count)
    (next : Actor δ α) : State δ α count :=
  { state with actors := fun index => if index = actor then next else state.actors index }

inductive Event (count : Nat) where
  | commit (actor : Fin count)
  | resume (actor : Fin count)
  | crash (actor : Fin count)
  | restart (actor : Fin count)
  | commitOrphan (index : Nat)
  | discardOrphan (index : Nat)
  deriving Repr, BEq, DecidableEq

inductive Error where
  | notWaiting | notResponding | notRunning | notStopped | noOrphan
  deriving Repr, BEq, DecidableEq

/-- One externally chosen event. Crashes preserve already committed state and
retain remote requests for possible later commitment. Local DB calls cannot
survive a scheduler crash and overwrite its recovered state. -/
def step (start : Start δ α count) (event : Event count) (state : State δ α count) :
    Except Error (State δ α count) :=
  match event with
  | .commit actor =>
    match state.actors actor with
    | .waiting _ _ operation next =>
      let (value, world) := operation state.world
      .ok { state.setActor actor (.responding value next) with world }
    | _ => .error .notWaiting
  | .resume actor =>
    match state.actors actor with
    | .responding value next => .ok (state.setActor actor (.ofProgram (ArrsF.apply next value)))
    | _ => .error .notResponding
  | .crash actor =>
    match state.actors actor with
    | .waiting remote label operation _ =>
      let orphans := if remote then state.orphans.push ⟨label, fun world => (operation world).2⟩ else state.orphans
      .ok { state.setActor actor .stopped with orphans }
    | .responding .. => .ok (state.setActor actor .stopped)
    | _ => .error .notRunning
  | .restart actor =>
    match state.actors actor with
    | .stopped =>
      let generation := state.generations actor + 1
      .ok { state.setActor actor (.ofProgram (start actor generation)) with
        generations := fun index => if index = actor then generation else state.generations index }
    | _ => .error .notStopped
  | .commitOrphan index =>
    if h : index < state.orphans.size then
      let orphan := state.orphans[index]
      let world := orphan.commit state.world
      .ok { state with world, orphans := state.orphans.eraseIdx index }
    else .error .noOrphan
  | .discardOrphan index =>
    if h : index < state.orphans.size then .ok { state with orphans := state.orphans.eraseIdx index }
    else .error .noOrphan

def run (start : Start δ α count) (events : List (Event count)) (state : State δ α count) :
    Except Error (State δ α count) :=
  events.foldlM (fun state event => step start event state) state

end Simulation
end LeanCloud
