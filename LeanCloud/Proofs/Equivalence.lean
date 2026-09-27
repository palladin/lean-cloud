import LeanCloud.Proofs.ReplayExecution
import LeanCloud.Proofs.Evaluation

/-! Observations compared by the equivalence theorem in `WholeRun.lean`. Replay uses the ideal
stack queue, which preserves the sequential reference's effect order. No
statement here identifies arbitrary reorderings of stateful effects. -/

namespace LeanCloud.Proofs
open Lean LeanEff

abbrev Observation (World α : Type) := Except CloudError α × World

def runDirect (blobs : BlobModel World) (program : ι → Cloud (StateM World) α)
    (input : ι) (world : World) : Observation World α :=
  let ((outcome, _), world) := (DirectInterpreter.interpret (modelStorage blobs) program input).run Journal.empty world
  (outcome, world)

def runReplay [Codec α] (blobs : BlobModel World) (fuel : Nat)
    (program : ι → Cloud (StateM World) α) (input : ι) (world : World) : Observation World α :=
  let ((outcome, _), world) := (LeanCloud.interpret (ReplayModel.storage blobs) ReplayModel.queue fuel program input).run
    ReplayModel.initial world
  (outcome, world)

/-- The full target, including parallel groups, errors, and external state.
The queue order is explicit; fairness alone is not an effect-commutativity law. -/
def FreshRunEquivalence : Prop :=
  ∀ {World ι α : Type} [codec : Codec α]
    (blobs : BlobModel World) (program : ι → Cloud (StateM World) α)
    (input : ι) (world : World),
    CodecLaw codec → Supported (program input) →
    ∃ bound, ∀ fuel, bound ≤ fuel →
      runReplay blobs fuel program input world = runDirect blobs program input world

end LeanCloud.Proofs
