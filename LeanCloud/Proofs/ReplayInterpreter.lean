import LeanCloud.Proofs.Codecs
import LeanCloud.Proofs.DirectInterpreter
import LeanCloud.Proofs.Location
import LeanCloud.Proofs.Model
import LeanCloud.Proofs.Parallel

/-! Reconstruction laws for the actual replay loop in the ideal storage model.
These are local laws, not the full fresh-run equivalence theorem. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

variable {World α : Type}

/-- Evaluate a monadic bind at concrete journal and world states. -/
theorem run_bind_state {α β : Type}
    (action : ExceptT CloudError (StateT Journal (StateM World)) α)
    (next : α → ExceptT CloudError (StateT Journal (StateM World)) β)
    (journal : Journal) (world : World) :
    (action >>= next).run journal world =
      let ((outcome, journal'), world') := action.run journal world
      match outcome with
      | .ok value => (next value).run journal' world'
      | .error error => ((.error error, journal'), world') := by
  dsimp [ExceptT.run, bind, ExceptT.bind, ExceptT.bindCont, StateT.bind]
  cases action journal world with
  | mk pair world' => cases pair with
    | mk outcome journal' => cases outcome <;> rfl

theorem run_pure_state (value : α) (journal : Journal) (world : World) :
    (pure value : ExceptT CloudError (StateT Journal (StateM World)) α).run journal world =
      ((.ok value, journal), world) := rfl

theorem run_tryCatch_state
    (action : ExceptT CloudError (StateT Journal (StateM World)) α)
    (handle : CloudError → ExceptT CloudError (StateT Journal (StateM World)) α)
    (journal : Journal) (world : World) :
    (tryCatch action handle).run journal world =
      let ((outcome, journal'), world') := action.run journal world
      match outcome with
      | .ok value => ((.ok value, journal'), world')
      | .error error => (handle error).run journal' world' := by
  dsimp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch,
    ExceptT.run, bind, StateT.bind]
  cases action journal world with
  | mk pair world' => cases pair with
    | mk outcome journal' => cases outcome <;> rfl

theorem load_recorded (blobs : BlobModel World) (journal : Journal) (world : World)
    (location : Location) (result : Result)
    (recorded : journal location.key = some (toJson result)) :
    (load (modelStorage blobs) location).run journal world =
      ((.ok (some result), journal), world) := by
  dsimp [load, modelStorage, ExceptT.run, bind, pure, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, StateT.bind, StateT.pure, Functor.map, StateT.map]
  simp only [recorded, result_roundtrip]
  rfl

theorem load_missing (blobs : BlobModel World) (journal : Journal) (world : World)
    (location : Location) (missing : journal location.key = none) :
    (load (modelStorage blobs) location).run journal world =
      ((.ok none, journal), world) := by
  dsimp [load, modelStorage, ExceptT.run, bind, pure, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, StateT.bind, StateT.pure, Functor.map, StateT.map]
  rw [missing]
  rfl

theorem save_result (blobs : BlobModel World) (journal : Journal) (world : World)
    (location : Location) (result : Result) :
    (save (modelStorage blobs) location result).run journal world =
      ((.ok (), journal.write location.key (toJson result)), world) := by
  rfl

theorem decode_encoded {m : Type → Type} [Monad m] (codec : Codec α)
    (law : CodecLaw codec) (value : α) :
    decode (m := m) codec (codec.encode value) = pure value := by
  simp only [decode, law value]

theorem walk_delay (blobs : BlobModel World) (root : Cloud (StateM World) Json)
    (fuel : Nat) (continuation : ArrsF (Control (StateM World)) Unit Json)
    (current target : Location) :
    step.walk (modelStorage blobs) root (fuel + 1) (.impure .delay continuation) current target =
      step.walk (modelStorage blobs) root fuel (ArrsF.apply continuation ()) current target := by
  rw [step.walk]

/-- A recorded successful effect restores its continuation without running the
operation, changing the journal, or changing the external world. -/
theorem walk_recorded_sequential (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat)
    (codec : Codec α) (law : CodecLaw codec) (operation : Operation (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) α Json) (value : α)
    (current target : Location) (journal : Journal) (world : World)
    (recorded : journal current.key = some (toJson (Result.completed (.success (codec.encode value))))) :
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.sequential codec operation) continuation) current target).run journal world =
    (step.walk (modelStorage blobs) root fuel (ArrsF.apply continuation value)
      current.next target).run journal world := by
  rw [step.walk]
  simp only [run_bind_state, load_recorded blobs journal world current _ recorded,
    run_pure_state, decode_encoded codec law value]

/-- At a missing journal entry, a successful primitive effect runs once and its
result is committed before resuming. The continuation sees its resulting world. -/
theorem walk_fresh_sequential (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat)
    (codec : Codec α) (law : CodecLaw codec) (operation : Operation (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) α Json) (value : α)
    (current target : Location) (journal : Journal) (world nextWorld : World)
    (atFrontier : current.before target = false)
    (missing : journal current.key = none)
    (executed : ((modelStorage blobs).execute operation).run journal world =
      ((.ok value, journal), nextWorld)) :
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.sequential codec operation) continuation) current target).run journal world =
    (step.walk (modelStorage blobs) root fuel (ArrsF.apply continuation value)
      current.next target).run
      (journal.write current.key (toJson (Result.completed (.success (codec.encode value)))))
      nextWorld := by
  rw [step.walk]
  simp only [run_bind_state, load_missing blobs journal world current missing,
    atFrontier, Bool.false_eq_true, ↓reduceIte, run_tryCatch_state, executed,
    run_pure_state, save_result, decode_encoded codec law value]

theorem failure_bne_self (error : CloudError) :
    (Exit.failure error != Exit.failure error) = false := by
  rcases error with ⟨kind, message⟩
  cases kind <;>
    simp [bne, BEq.beq, instBEqExit.beq, instBEqCloudError.beq, instBEqErrorKind.beq]

/-- A fresh primitive failure follows the same completion path as an explicit
failure, after retaining the primitive's world changes. The internal save and
read-back do not duplicate its execution or consume an extra loop iteration. -/
theorem walk_fresh_sequential_failure (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat)
    (codec : Codec α) (operation : Operation (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) α Json) (error : CloudError)
    (current target : Location) (journal : Journal) (world nextWorld : World)
    (atFrontier : current.before target = false)
    (missing : journal current.key = none)
    (executed : ((modelStorage blobs).execute operation).run journal world =
      ((.error error, journal), nextWorld)) :
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.sequential codec operation) continuation) current target).run journal world =
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.fail error) continuation) current target).run journal nextWorld := by
  have recorded :
      (journal.write current.key (toJson (Result.completed (.failure error)))) current.key =
        some (toJson (Result.completed (.failure error))) := by
    simp [Journal.write]
  conv => lhs; rw [step.walk]
  conv => rhs; rw [step.walk]
  simp only [run_bind_state, load_missing blobs journal world current missing,
    load_missing blobs journal nextWorld current missing,
    atFrontier, Bool.false_eq_true, ↓reduceIte, run_tryCatch_state, executed,
    run_pure_state, save_result,
    load_recorded blobs _ nextWorld current _ recorded, failure_bne_self]

/-- A completed group restores the ordered result array without evaluating its
branches again. The target remains in the current branch. -/
theorem walk_recorded_parallel (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat)
    (codec : Codec α) (law : CodecLaw codec) (count : Nat)
    (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json) (values : Array α)
    (current target : Location) (journal : Journal) (world : World)
    (sameBranch : current.entersChild target = false)
    (recorded : journal current.key =
      some (toJson (Result.completed (.success (Json.arr (values.map codec.encode)))))) :
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.parallel codec count branches) continuation) current target).run journal world =
    (step.walk (modelStorage blobs) root fuel (ArrsF.apply continuation values)
      current.next target).run journal world := by
  letI : Codec α := codec
  have decoded := decode_encoded (m := StateT Journal (StateM World))
    (inferInstance : Codec (Array α)) (codec_array law) values
  change decode (m := StateT Journal (StateM World)) (inferInstance : Codec (Array α))
    (Json.arr (values.map codec.encode)) = pure values at decoded
  rw [step.walk]
  simp only [sameBranch, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    run_bind_state, load_recorded blobs journal world current _ recorded,
    run_pure_state, decoded]

/-- A completed failed group follows the explicit-failure path; its continuation
and its children are not evaluated again. -/
theorem walk_recorded_parallel_failure (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json) (error : CloudError)
    (current target : Location) (journal : Journal) (world : World)
    (sameBranch : current.entersChild target = false)
    (recorded : journal current.key = some (toJson (Result.completed (.failure error)))) :
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.parallel codec count branches) continuation) current target).run journal world =
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.fail error) continuation) current target).run journal world := by
  conv => lhs; rw [step.walk]
  conv => rhs; rw [step.walk]
  simp only [sameBranch, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    run_bind_state, load_recorded blobs journal world current _ recorded, run_pure_state]

/-- An unresolved group at the requested frontier suspends with no additional
effects or storage writes, retaining the remaining fuel. -/
theorem walk_suspended_parallel (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json)
    (current target : Location) (journal : Journal) (world : World)
    (children : Array (Option Exit)) (size : children.size = count)
    (sameBranch : current.entersChild target = false)
    (atFrontier : current.before target = false)
    (recorded : journal current.key = some (toJson (Result.suspended children))) :
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.parallel codec count branches) continuation) current target).run journal world =
      ((.ok (.suspended current fuel), journal), world) := by
  rw [step.walk]
  simp only [sameBranch, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    run_bind_state, load_recorded blobs journal world current _ recorded,
    run_pure_state, size, bne_self_eq_false, atFrontier]

/-- The requested child is selected from the original branches, so it retains
the captured lexical environment. Selecting it does not run a sibling. -/
theorem walk_parallel_child (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat)
    (codec : Codec α) (count : Nat) (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json)
    (current target : Location) (journal : Journal) (world : World)
    (children : Array (Option Exit)) (size : children.size = count)
    (enters : current.entersChild target = true)
    (index : Fin count) (selected : target[current.size]!.1 = index.val)
    (recorded : journal current.key = some (toJson (Result.suspended children))) :
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.parallel codec count branches) continuation) current target).run journal world =
    (step.walk (modelStorage blobs) root fuel (codec.encode <$> branches index)
      (current.child index.val) target).run journal world := by
  rw [step.walk]
  simp only [enters, selected, index.isLt, Nat.not_le_of_lt index.isLt,
    decide_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
    run_bind_state, load_recorded blobs journal world current _ recorded,
    run_pure_state, size, bne_self_eq_false, ↓reduceDIte]

/-- A fresh nonempty group records exactly one empty slot per child and suspends
without executing a branch or changing the external world. -/
theorem walk_fresh_parallel (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat)
    (codec : Codec α) (count : Nat) (positive : 0 < count)
    (branches : Fin count → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json)
    (current target : Location) (journal : Journal) (world : World)
    (sameBranch : current.entersChild target = false)
    (atFrontier : current.before target = false)
    (missing : journal current.key = none) :
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.parallel codec count branches) continuation) current target).run journal world =
      ((.ok (.suspended current fuel),
        journal.write current.key (toJson (Result.suspended (Array.replicate count none)))), world) := by
  have waiting : Result.settle (Array.replicate count none) =
      .suspended (Array.replicate count none) := by
    apply Result.settle_missing
    simp [Array.mem_replicate, Nat.ne_of_gt positive]
  rw [step.walk]
  simp only [sameBranch, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    run_bind_state, load_missing blobs journal world current missing, atFrontier,
    waiting, save_result, run_pure_state, Array.size_replicate, bne_self_eq_false]

/-- An empty group records its empty result and immediately resumes. No element
codec is invoked, so no codec-law premise is needed for this case. -/
theorem walk_fresh_empty_parallel (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat) (codec : Codec α)
    (branches : Fin 0 → Cloud (StateM World) α)
    (continuation : ArrsF (Control (StateM World)) (Array α) Json)
    (current target : Location) (journal : Journal) (world : World)
    (sameBranch : current.entersChild target = false)
    (atFrontier : current.before target = false)
    (missing : journal current.key = none) :
    (step.walk (modelStorage blobs) root (fuel + 1)
      (.impure (.parallel codec 0 branches) continuation) current target).run journal world =
    (step.walk (modelStorage blobs) root fuel (ArrsF.apply continuation #[]) current.next target).run
      (journal.write current.key (toJson (Result.completed (.success (Json.arr #[]))))) world := by
  letI : Codec α := codec
  have decoded : decode (m := StateT Journal (StateM World))
      (inferInstance : Codec (Array α)) (Json.arr #[]) = pure #[] := by
    have emptyDecode : (inferInstance : Codec (Array α)).decode (Json.arr #[]) = .ok #[] := by
      change (#[] : Array Json).mapM codec.decode = .ok #[]
      simpa [pure, Except.pure] using (Array.mapM_empty (m := Except String) codec.decode)
    simp only [decode, emptyDecode]
  rw [step.walk]
  simp only [sameBranch, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    run_bind_state, load_missing blobs journal world current missing, atFrontier,
    Array.replicate_zero, Result.settle_empty, save_result, run_pure_state, decoded]

end LeanCloud.Proofs
