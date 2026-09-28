import LeanCloud.Proofs.ReplayModel
import LeanCloud.Proofs.Codecs
import LeanCloud.Proofs.Location

/-! Equations for the current replay step in the ideal environment. -/

namespace LeanCloud.Proofs.ReplayModel
open Lean LeanEff ReplayInterpreter.Internal

variable {α : Type}

theorem run_pure (value : α) (state : State) :
    (pure value : ExceptT CloudError (StateT State Id) α).run state =
      ((.ok value, state)) := rfl

theorem load_recorded (state : State) (location : Location) (result : Result)
    (recorded : state.journal location.key = some (toJson result)) :
    (load db location).run state = ((.ok (some result), state)) := by
  dsimp [load, db, ExceptT.run, bind, pure, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, StateT.bind, StateT.pure, Functor.map, StateT.map]
  simp only [recorded, result_roundtrip]
  rfl

theorem load_missing (state : State) (location : Location) (missing : state.journal location.key = none) :
    (load db location).run state = ((.ok none, state)) := by
  dsimp [load, db, ExceptT.run, bind, pure, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, StateT.bind, StateT.pure, Functor.map, StateT.map]
  rw [missing]
  rfl

theorem save_result (state : State) (location : Location) (result : Result) :
    (save db location result).run state =
      ((.ok (), {state with journal := state.journal.write location.key (toJson result)})) := rfl

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

theorem finish_fresh_root (current : Location) (outcome : Exit)
    (state : State) (missing : state.journal current.key = none)
    (noParent : current.parent? = none) :
    (finish db current outcome).run state =
      ((.ok (.done outcome), {state with journal := state.journal.write current.key (toJson (Result.completed outcome))})) := by
  rw [finish]
  simp only [run_bind, load_missing state current missing, save_result, noParent, run_pure]

theorem walk_recorded_parallel (fuel : Nat)
    (codec : Codec α) (law : CodecLaw codec) (count : Nat)
    (branches : Fin count → Cloud Id α)
    (continuation : ArrsF (Control Id) (Array α) Json) (values : Array α)
    (current target : Location) (state : State) (size : values.size = count) (different : current ≠ target)
    (recorded : state.journal current.key =
      some (toJson (Result.completed (.success (Json.arr (values.map codec.encode)))))) :
    (walk db noBlobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current target).run state =
      (walk db noBlobs fuel (ArrsF.apply continuation values) current.next target).run state := by
  rw [walk]
  simp only [run_bind, load_recorded state current _ recorded,
    beq_eq_false_iff_ne.mpr different, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    run_pure, ← size, decode_group_encoded codec law values]

theorem walk_parallel_child (fuel : Nat)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud Id α)
    (continuation : ArrsF (Control Id) (Array α) Json)
    (current target : Location) (state : State) (children : Array (Option Exit)) (size : children.size = count)
    (enters : current.entersChild target = true) (index : Fin count)
    (selected : target[current.size]!.1 = index.val)
    (recorded : state.journal current.key = some (toJson (Result.suspended children))) :
    (walk db noBlobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current target).run state =
      (walk db noBlobs fuel (codec.encode <$> branches index) (current.child index.val) target).run state := by
  have different : current ≠ target := by
    intro same
    subst target
    simp [Location.entersChild] at enters
  rw [walk]
  simp only [run_bind, load_recorded state current _ recorded,
    beq_eq_false_iff_ne.mpr different, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    size, bne_self_eq_false, enters, Bool.not_true, selected, index.isLt, ↓reduceDIte]

theorem walk_delay (fuel : Nat)
    (continuation : ArrsF (Control Id) Unit Json) (current target : Location) :
    walk db noBlobs (fuel + 1) (.impure .delay continuation) current target =
      walk db noBlobs fuel (ArrsF.apply continuation ()) current target := rfl

theorem walk_fresh_parallel (fuel : Nat) (codec : Codec α)
    (count : Nat) (branches : Fin count → Cloud Id α)
    (continuation : ArrsF (Control Id) (Array α) Json)
    (current : Location) (state : State) (missing : state.journal current.key = none) :
    (walk db noBlobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current current).run state =
      ((.ok (.runnable (if count == 0 then #[current] else Array.ofFn fun i : Fin count => current.child i.val)),
        {state with journal := state.journal.write current.key (toJson (Result.settle (Array.replicate count none)))})) := by
  rw [walk]
  simp only [run_bind, load_missing state current missing, beq_self_eq_true,
    Option.isNone_none, Bool.and_true, ↓reduceIte, save_result, run_pure]

theorem walk_join_parallel (fuel : Nat)
    (codec : Codec α) (law : CodecLaw codec) (count : Nat)
    (branches : Fin count → Cloud Id α)
    (continuation : ArrsF (Control Id) (Array α) Json) (values : Array α)
    (current : Location) (state : State) (size : values.size = count)
    (recorded : state.journal current.key =
      some (toJson (Result.completed (.success (Json.arr (values.map codec.encode)))))) :
    (walk db noBlobs (fuel + 1) (.impure (.parallel codec count branches) continuation) current current).run state =
      ((.ok (.runnable #[current.next]), state)) := by
  rw [walk]
  simp only [run_bind, load_recorded state current _ recorded, beq_self_eq_true,
    Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    ← size, decode_group_encoded codec law values, run_pure]

/-- The parent of a pending item is still waiting for its result. -/
def ParentOpen (journal : Journal) (location : Location) : Prop :=
  ∀ parent index, location.parent? = some (parent, index) →
    ∃ children, journal parent.key = some (toJson (Result.suspended children))

/-- Valid pending locations pass the worker entry point's guards. -/
theorem step_eq_walk {journal : Journal} {root : Cloud Id Json} {target : Location}
    (nonempty : 0 < target.size) (rootBranch : target[0]!.1 = 0)
    (parentOpen : ParentOpen journal target) (fuel : Nat) (pending : List Location) :
    (step db noBlobs fuel root target).run ⟨journal, pending, none⟩ =
      (walk db noBlobs fuel root Location.root target).run ⟨journal, pending, none⟩ := by
  have notEmpty : target.isEmpty = false := by
    simp [Array.isEmpty, Nat.ne_of_gt nonempty]
  rw [step]
  simp only [notEmpty, rootBranch, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  cases parentEq : target.parent? with
  | none => rfl
  | some pair =>
    obtain ⟨parent, index⟩ := pair
    obtain ⟨children, recorded⟩ := parentOpen parent index parentEq
    simp only [run_bind, load_recorded ⟨journal, pending, none⟩ parent _ recorded]

end LeanCloud.Proofs.ReplayModel
