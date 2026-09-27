import LeanCloud.Proofs.Equivalence
import LeanCloud.Proofs.TraversalCorrectness

/-! Equivalence of the actual public direct and replay interpreters.

Finite direct evaluation supplies a replay traversal. Each traversal consists of
proved runtime steps under the ideal stack queue, so it determines a sufficient
fuel bound. The final comparison includes both the returned value/error and the
external world. The journal and pending queue are replay bookkeeping.

Scope: fresh runs, sequential effect order, total StateM effects, lawful codecs,
and the supported language (no choice). Restart and arbitrary interleaving are
separate properties; neither is assumed or claimed here. -/

namespace LeanCloud.Proofs
open Lean LeanEff ReplayModel

/-- A traversal at the root gives equality of both public interpreter observations. -/
theorem equivalence_of_traversal {World ι α : Type} [codec : Codec α]
    (blobs : BlobModel World) (program : ι → Cloud (StateM World) α) (input : ι)
    (initialWorld finalWorld : World) (outcome : Except CloudError α) (work : Nat)
    (law : CodecLaw codec)
    (execution : Evaluation blobs (program input) initialWorld outcome finalWorld work)
    (traversal : BranchTraversal blobs (codec.encode <$> program input)
      Location.root Journal.empty initialWorld (outcome.map codec.encode) finalWorld) :
    ∃ requiredFuel : Nat, ∀ fuel, requiredFuel ≤ fuel →
      runReplay blobs fuel program input initialWorld = runDirect blobs program input initialWorld := by
  have segment := traversal.correct .root [] rfl
  change Segment blobs (codec.encode <$> program input) initial initialWorld
    ⟨traversal.finalJournal.write traversal.location.key
        (toJson (Result.completed (encoded (outcome.map codec.encode)))),
      [], some (encoded (outcome.map codec.encode))⟩ finalWorld at segment
  obtain ⟨bound, finished⟩ := segment.finished (α := α)
  have decoded : decodeExit (encoded (outcome.map codec.encode)) = outcome := by
    cases outcome with
    | error error => rfl
    | ok value => exact decodeExit_encoded law value
  refine ⟨bound, ?_⟩
  intro fuel enough
  have replay := finished fuel enough
  rw [decoded] at replay
  unfold runReplay LeanCloud.interpret
  rw [replay]
  unfold runDirect DirectInterpreter.interpret
  rw [execution.sound]

/-- With the ideal stack queue, every supported fresh workflow agrees with the
sequential direct interpreter on its value/error and final external world.
There exists a fuel bound that works for every larger budget. -/
theorem freshRunEquivalence : FreshRunEquivalence := by
  intro World ι α codec blobs program input initialWorld law supported
  obtain ⟨outcome, finalWorld, work, execution⟩ := Evaluation.exists blobs (program input) supported initialWorld
  obtain ⟨traversal⟩ := ReplayModel.Evaluation.traverse (execution.map codec.encode)
    (codec.encode <$> program input) Location.root Journal.empty 0
    (ReplayRoute.initial _) (Journal.Fresh.empty _)
  exact equivalence_of_traversal blobs program input initialWorld finalWorld outcome work law execution traversal

/-- Same input, same returned value or typed error, for every sufficiently large
fuel budget under the ideal queue's sequential effect order. -/
theorem same_output {World ι α : Type} [codec : Codec α]
    (blobs : BlobModel World) (program : ι → Cloud (StateM World) α)
    (input : ι) (initialWorld : World) (law : CodecLaw codec) (supported : Supported (program input)) :
    ∃ requiredFuel : Nat, ∀ fuel : Nat, requiredFuel ≤ fuel →
      (runReplay blobs fuel program input initialWorld).1 =
        (runDirect blobs program input initialWorld).1 := by
  obtain ⟨requiredFuel, agrees⟩ := freshRunEquivalence blobs program input initialWorld law supported
  exact ⟨requiredFuel, fun fuel enough => congrArg Prod.fst (agrees fuel enough)⟩

end LeanCloud.Proofs
