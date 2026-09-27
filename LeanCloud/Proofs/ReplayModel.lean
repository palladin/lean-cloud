import LeanCloud.ReplayInterpreter
import LeanCloud.Proofs.Model
import LeanCloud.Proofs.Storage

/-! Ideal environment for the actual replay interpreter. Work is kept in a
stack: each step replaces the selected head with its successors in array order.
This gives the sequential reference's effect order, including nested groups.
The environment never inspects the program or manufactures its final outcome. -/

namespace LeanCloud.Proofs.ReplayModel
open Lean

structure State where
  journal : Journal := Journal.empty
  pending : List Location := [Location.root]
  completed : Option Exit := none

def storage (blobs : BlobModel World) : Storage State (StateM World) where
  get key state := pure (state.journal key, state)
  put key value state := pure (true, { state with journal := state.journal.write key value })
  putBlob bytes state := do
    let outcome ← (blobs.putBlob bytes).run
    pure (outcome, state)
  readBlob ref state := do
    let outcome ← (blobs.readBlob ref).run
    pure (outcome, state)
  resolveBlob name state := do
    let outcome ← (blobs.resolveBlob name).run
    pure (outcome, state)

def update (state : State) (location : Location) : StepResult → State
  | .runnable locations => { state with pending := locations.toList ++ state.pending.erase location }
  | .done outcome => { state with pending := [], completed := some outcome }

def queue : WorkQueue State (StateM World) where
  next state := pure ((match state.completed with
    | some outcome => .completed outcome
    | none => match state.pending with
      | [] => .idle
      | location :: _ => .item location), state)
  complete location result state := pure ((), update state location result)

def initial : State := {}

theorem execute (blobs : BlobModel World) (operation : Operation (StateM World) α)
    (state : State) (world : World) :
    ((storage blobs).execute operation).run state world =
      let ((outcome, _), nextWorld) := ((modelStorage blobs).execute operation).run Journal.empty world
      ((outcome, state), nextWorld) := by
  cases operation with
  | exec label body =>
    cases h : body () world with
    | mk value nextWorld =>
      simp [Storage.execute, ExceptT.run, ExceptT.mk, liftM, monadLift,
        MonadLift.monadLift, ExceptT.lift, StateT.lift, Functor.map, StateT.map,
        bind, pure, StateT.bind, StateT.pure, h]
  | putBlob bytes => rfl
  | readBlob ref => rfl
  | resolveBlob name => rfl

theorem run_bind {α β : Type}
    (action : ExceptT CloudError (StateT State (StateM World)) α)
    (next : α → ExceptT CloudError (StateT State (StateM World)) β)
    (state : State) (world : World) :
    (action >>= next).run state world =
      let ((outcome, state'), world') := action.run state world
      match outcome with
      | .ok value => (next value).run state' world'
      | .error error => ((.error error, state'), world') := by
  dsimp [ExceptT.run, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind]
  cases action state world with
  | mk pair world' => cases pair with
    | mk outcome state' => cases outcome <;> rfl

theorem update_head (journal : Journal) (location : Location) (rest : List Location)
    (locations : Array Location) :
    update ⟨journal, location :: rest, none⟩ location (.runnable locations) =
      ⟨journal, locations.toList ++ rest, none⟩ := by
  simp [update]

theorem next_head (journal : Journal) (location : Location) (rest : List Location) (world : World) :
    (queue (World := World)).next ⟨journal, location :: rest, none⟩ world =
      ((.item location, ⟨journal, location :: rest, none⟩), world) := rfl

end LeanCloud.Proofs.ReplayModel
