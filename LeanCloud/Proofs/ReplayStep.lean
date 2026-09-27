import LeanCloud.Proofs.ReplayModel
import LeanCloud.Proofs.Codecs
import LeanCloud.Proofs.Location

/-! Equations for the current replay step in the ideal environment. -/

namespace LeanCloud.Proofs.ReplayModel
open Lean LeanEff ReplayInterpreter.Internal

variable {World α : Type}

theorem run_pure (value : α) (state : State) (world : World) :
    (pure value : ExceptT CloudError (StateT State (StateM World)) α).run state world =
      ((.ok value, state), world) := rfl

theorem run_catch
    (action : ExceptT CloudError (StateT State (StateM World)) α)
    (handle : CloudError → ExceptT CloudError (StateT State (StateM World)) α)
    (state : State) (world : World) :
    (tryCatch action handle).run state world =
      let ((outcome, state'), world') := action.run state world
      match outcome with
      | .ok value => ((.ok value, state'), world')
      | .error error => (handle error).run state' world' := by
  dsimp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch,
    ExceptT.run, bind, StateT.bind]
  cases action state world with
  | mk pair world' => cases pair with
    | mk outcome state' => cases outcome <;> rfl

theorem load_recorded (blobs : BlobModel World) (state : State) (world : World)
    (location : Location) (result : Result)
    (recorded : state.journal location.key = some (toJson result)) :
    (load (storage blobs) location).run state world = ((.ok (some result), state), world) := by
  dsimp [load, storage, ExceptT.run, bind, pure, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, StateT.bind, StateT.pure, Functor.map, StateT.map]
  simp only [recorded, result_roundtrip]
  rfl

theorem load_missing (blobs : BlobModel World) (state : State) (world : World)
    (location : Location) (missing : state.journal location.key = none) :
    (load (storage blobs) location).run state world = ((.ok none, state), world) := by
  dsimp [load, storage, ExceptT.run, bind, pure, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, StateT.bind, StateT.pure, Functor.map, StateT.map]
  rw [missing]
  rfl

theorem save_result (blobs : BlobModel World) (state : State) (world : World)
    (location : Location) (result : Result) :
    (save (storage blobs) location result).run state world =
      ((.ok (), { state with journal := state.journal.write location.key (toJson result) }), world) := rfl

theorem decode_encoded {m : Type → Type} [Monad m] (codec : Codec α)
    (law : CodecLaw codec) (value : α) :
    decode (m := m) codec (codec.encode value) = pure value := by
  simp only [decode, law value]

theorem decode_group_encoded {m : Type → Type} [Monad m] [LawfulMonad m] (codec : Codec α)
    (law : CodecLaw codec) (values : Array α) :
    decodeGroup (m := m) codec values.size (Json.arr (values.map codec.encode)) = pure values := by
  letI : Codec α := codec
  have decoded := decode_encoded (m := m) (inferInstance : Codec (Array α)) (codec_array law) values
  change decode (m := m) (inferInstance : Codec (Array α)) (Json.arr (values.map codec.encode)) = pure values at decoded
  simp [decodeGroup, decoded]

theorem walk_recorded_sequential (blobs : BlobModel World) (fuel : Nat)
    (codec : Codec α) (law : CodecLaw codec) (operation : Operation (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) α Json) (value : α)
    (current target : Location) (state : State) (world : World)
    (different : current ≠ target)
    (recorded : state.journal current.key = some (toJson (Result.completed (.success (codec.encode value))))) :
    (walk (storage blobs) (fuel + 1) (.impure (.sequential codec operation) continuation) current target).run state world =
      (walk (storage blobs) fuel (ArrsF.apply continuation value) current.next target).run state world := by
  rw [walk]
  simp only [run_bind, load_recorded blobs state world current _ recorded, run_pure,
    decode_encoded codec law value, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte]

theorem walk_fresh_sequential (blobs : BlobModel World) (fuel : Nat)
    (codec : Codec α) (law : CodecLaw codec) (operation : Operation (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) α Json) (value : α)
    (current : Location) (state : State) (world nextWorld : World)
    (missing : state.journal current.key = none)
    (executed : ((storage blobs).execute operation).run state world = ((.ok value, state), nextWorld)) :
    (walk (storage blobs) (fuel + 1) (.impure (.sequential codec operation) continuation) current current).run state world =
      ((.ok (.runnable #[current.next]),
        { state with journal := state.journal.write current.key (toJson (Result.completed (.success (codec.encode value)))) }),
        nextWorld) := by
  rw [walk]
  simp only [run_bind, load_missing blobs state world current missing, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, run_catch, executed, run_pure, save_result,
    decode_encoded codec law value, beq_self_eq_true, ↓reduceIte]

theorem finish_fresh_root (blobs : BlobModel World) (current : Location) (outcome : Exit)
    (state : State) (world : World) (missing : state.journal current.key = none)
    (noParent : current.parent? = none) :
    (finish (storage blobs) current outcome).run state world =
      ((.ok (.done outcome), { state with journal := state.journal.write current.key (toJson (Result.completed outcome)) }), world) := by
  rw [finish]
  simp only [run_bind, load_missing blobs state world current missing, save_result, noParent, run_pure]

theorem step_root (blobs : BlobModel World) (fuel : Nat) (root : Cloud (StateM World) Json) :
    step (storage blobs) fuel root Location.root =
      walk (storage blobs) fuel root Location.root Location.root := by
  simp [step, Location.root, Location.parent?]

theorem walk_recorded_parallel (blobs : BlobModel World) (fuel : Nat)
    (codec : Codec α) (law : CodecLaw codec) (count : Nat)
    (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json) (values : Array α)
    (current target : Location) (state : State) (world : World)
    (size : values.size = count) (different : current ≠ target)
    (recorded : state.journal current.key =
      some (toJson (Result.completed (.success (Json.arr (values.map codec.encode)))))) :
    (walk (storage blobs) (fuel + 1) (.impure (.parallel codec count branches) continuation) current target).run state world =
      (walk (storage blobs) fuel (ArrsF.apply continuation values) current.next target).run state world := by
  rw [walk]
  simp only [run_bind, load_recorded blobs state world current _ recorded,
    beq_eq_false_iff_ne.mpr different, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    run_pure, ← size, decode_group_encoded codec law values]

theorem walk_parallel_child (blobs : BlobModel World) (fuel : Nat)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json)
    (current target : Location) (state : State) (world : World)
    (children : Array (Option Exit)) (size : children.size = count)
    (enters : current.entersChild target = true) (index : Fin count)
    (selected : target[current.size]!.1 = index.val)
    (recorded : state.journal current.key = some (toJson (Result.suspended children))) :
    (walk (storage blobs) (fuel + 1) (.impure (.parallel codec count branches) continuation) current target).run state world =
      (walk (storage blobs) fuel (codec.encode <$> branches index) (current.child index.val) target).run state world := by
  have different : current ≠ target := by
    intro same
    subst target
    simp [Location.entersChild] at enters
  rw [walk]
  simp only [run_bind, load_recorded blobs state world current _ recorded,
    beq_eq_false_iff_ne.mpr different, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    size, bne_self_eq_false, enters, Bool.not_true, selected, index.isLt, ↓reduceDIte]

theorem walk_delay (blobs : BlobModel World) (fuel : Nat)
    (continuation : ArrsF (Control (StateM World)) Unit Json) (current target : Location) :
    walk (storage blobs) (fuel + 1) (.impure .delay continuation) current target =
      walk (storage blobs) fuel (ArrsF.apply continuation ()) current target := rfl

end LeanCloud.Proofs.ReplayModel
