import LeanCloud.Proofs.Equivalence
import LeanCloud.Proofs.Traversal
import LeanCloud.Proofs.TraversalCorrectness

/-! Whole-run equivalence of the existing direct and replay interpreters.

The proof has three stages:
1. `Evaluation.exists` derives a finite evaluation for every supported program;
   `Evaluation.sound` connects it to the actual direct interpreter.
2. `Evaluation.traverse` follows that evaluation through the actual replay
   interpreter. Journal freshness prevents collisions; replay routes reconstruct
   recorded prefixes; parallel traversal runs each child in array order.
3. `equivalence_of_traversal` supplies enough fuel to finish the root and compares
   the returned value or error and final external state. Every larger budget works.

`freshRunEquivalence` composes these stages. `same_output` projects the output.
The scope is fresh runs in the ideal model, with lawful codecs and no choice. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayInterpreter.Internal

theorem run_root_eq_driveWalk {World α : Type} [Codec α] (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (fuel : Nat) :
    LeanCloud.interpret.run (α := α) (modelStorage blobs) fuel root Location.root =
      driveWalk blobs fuel root root Location.root Location.root := by
  rw [run_eq_step]
  rfl

/-- A root terminal result returns the typed value or error and leaves the
external world unchanged. A previously recorded group failure is also accepted. -/
theorem terminal_root {World α : Type} [codec : Codec α] (blobs : BlobModel World)
    (root : Cloud (StateM World) Json) (law : CodecLaw codec) (outcome : Except CloudError α)
    (location : Location) (journal : Journal) (world : World) (fuel : Nat)
    (positive : 0 < fuel) (nonempty : 0 < location.size) (noParent : location.parent? = none)
    (ready : ReturnReady journal location (outcome.map codec.encode)) :
    ∃ finalJournal,
      (driveWalk (α := α) blobs fuel root (terminalProgram (outcome.map codec.encode)) location location).run
        journal world = ((outcome, finalJournal), world) := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  cases outcome with
  | ok value =>
    cases ready with
    | fresh available =>
      refine ⟨journal.write location.key (toJson (Result.completed (.success (codec.encode value)))), ?_⟩
      rw [driveWalk, run_bind_state]
      simp only [Except.map, terminalProgram, step.walk, Location.before, Nat.lt_irrefl,
        decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, run_bind_state,
        load_missing blobs journal world location (available.missing nonempty), save_result,
        noParent, run_pure_state, continueStep, decode_encoded codec law value]
  | error error =>
    cases ready with
    | fresh available =>
      refine ⟨journal.write location.key (toJson (Result.completed (.failure error))), ?_⟩
      rw [driveWalk, run_bind_state]
      simp only [Except.map, terminalProgram, step.walk, Location.before, Nat.lt_irrefl,
        decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, run_bind_state,
        load_missing blobs journal world location (available.missing nonempty), save_result,
        noParent]
      rfl
    | failure _ recorded available =>
      refine ⟨journal, ?_⟩
      rw [driveWalk, run_bind_state]
      simp only [Except.map, terminalProgram, step.walk, Location.before, Nat.lt_irrefl,
        decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, run_bind_state,
        load_recorded blobs journal world location _ recorded, failure_bne_self,
        noParent]
      rfl

/-- Once branch traversal has been established for the encoded root, it implies
the complete required observation equality, with a bound valid for every larger
fuel budget. No assumption of interpreter equivalence occurs in this theorem. -/
theorem equivalence_of_traversal {World ι α : Type} [codec : Codec α]
    (blobs : BlobModel World) (program : ι → Cloud (StateM World) α) (input : ι)
    (initialWorld finalWorld : World) (outcome : Except CloudError α) (work : Nat)
    (law : CodecLaw codec)
    (execution : Evaluation blobs (program input) initialWorld outcome finalWorld work)
    (traversal : BranchTraversal (β := α) blobs (codec.encode <$> program input)
      (codec.encode <$> program input) Location.root Journal.empty initialWorld (outcome.map codec.encode) finalWorld) :
    ∃ requiredFuel : Nat, ∀ fuel, requiredFuel ≤ fuel →
      runReplay blobs fuel program input initialWorld = runDirect blobs program input initialWorld := by
  refine ⟨traversal.cost + 1, ?_⟩
  intro fuel enough
  have positive : 0 < fuel - traversal.cost := by omega
  have budget : fuel - traversal.cost + traversal.cost = fuel := by omega
  have traversed := traversal.correct (fuel - traversal.cost) positive
  rw [budget] at traversed
  have noParent : traversal.location.parent? = none := by
    rw [traversal.sameParent]
    rfl
  obtain ⟨finalJournal, finished⟩ := terminal_root blobs _ law outcome traversal.location traversal.finalJournal
    finalWorld (fuel - traversal.cost) positive traversal.nonempty noParent traversal.ready
  rw [finished] at traversed
  have replay : (LeanCloud.interpret (modelStorage blobs) fuel program input).run Journal.empty initialWorld =
      ((outcome, finalJournal), finalWorld) := by
    change (LeanCloud.interpret.run (α := α) (modelStorage blobs) fuel (codec.encode <$> program input)
      Location.root).run Journal.empty initialWorld = _
    rw [run_root_eq_driveWalk]
    exact traversed
  have direct := execution.sound
  unfold runReplay runDirect observeFresh
  rw [replay]
  change (outcome, finalWorld) =
    (let ((result, _), world) := (DirectInterpreter.Internal.eval (modelStorage blobs) (program input)).run
      Journal.empty initialWorld
     (result, world))
  rw [direct]

/-- Fresh replay and direct evaluation agree on the complete value or error and
final external world for every supported program and lawful result codec, once
sufficient fuel is supplied. This is the full `FreshRunEquivalence` statement. -/
theorem freshRunEquivalence : FreshRunEquivalence := by
  intro World ι α codec blobs program input initialWorld law supported
  obtain ⟨outcome, finalWorld, work, execution⟩ := Evaluation.exists blobs (program input) supported initialWorld
  have encoded := execution.map codec.encode
  obtain ⟨traversal⟩ := encoded.traverse (β := α) (codec.encode <$> program input) Location.root Journal.empty 0
    (ReplayRoute.initial _) (Journal.Fresh.empty _)
  exact equivalence_of_traversal blobs program input initialWorld finalWorld outcome work law execution traversal

/-- The direct and replay interpreters return the same value or error for the
same input, for every sufficiently large fuel budget. -/
theorem same_output {World ι α : Type} [codec : Codec α]
    (blobs : BlobModel World) (program : ι → Cloud (StateM World) α)
    (input : ι) (initialWorld : World) (law : CodecLaw codec) (supported : Supported (program input)) :
    ∃ requiredFuel : Nat, ∀ fuel : Nat, requiredFuel ≤ fuel →
      (runReplay blobs fuel program input initialWorld).1 =
        (runDirect blobs program input initialWorld).1 := by
  obtain ⟨requiredFuel, agrees⟩ := freshRunEquivalence blobs program input initialWorld law supported
  exact ⟨requiredFuel, fun fuel enough => congrArg Prod.fst (agrees fuel enough)⟩

end LeanCloud.Proofs
