import LeanCloud.DirectInterpreter
import LeanCloud.ReplayInterpreter
import LeanCloud.Proofs.Assumptions
import LeanCloud.Proofs.Model

/-! Observations and the fresh-run equivalence statement. The statement is proved
by `LeanCloud.Proofs.freshRunEquivalence` in `Proofs.WholeRun`. -/

namespace LeanCloud.Proofs

/-- Compare the outcome and external world while hiding replay bookkeeping.
The world may itself contain an effect trace if trace equality is desired. -/
abbrev Observation (World α : Type) := Except CloudError α × World

/-- Both initial runs begin with an empty journal. -/
def observeFresh (action : ExceptT CloudError (StateT Journal (StateM World)) α)
    (initialWorld : World) : Observation World α :=
  let ((outcome, _journal), finalWorld) := action.run Journal.empty initialWorld
  (outcome, finalWorld)

def runDirect (blobs : BlobModel World) (program : ι → Cloud (StateM World) α)
    (input : ι) (initialWorld : World) : Observation World α :=
  observeFresh (DirectInterpreter.interpret (modelStorage blobs) program input) initialWorld

def runReplay [Codec α] (blobs : BlobModel World) (fuel : Nat)
    (program : ι → Cloud (StateM World) α) (input : ι) (initialWorld : World) :
    Observation World α :=
  observeFresh (LeanCloud.interpret (modelStorage blobs) fuel program input) initialWorld

/-- Target: for every supported program with a lawful result codec, replay and
direct execution agree on the complete outcome and final external world once
enough fuel is supplied. The bound may depend on the model, program, input, and
initial world. It must work for every larger fuel budget as well.

The proof is `freshRunEquivalence` in `Proofs.WholeRun`. -/
def FreshRunEquivalence : Prop :=
  ∀ {World ι α : Type} [codec : Codec α]
    (blobs : BlobModel World) (program : ι → Cloud (StateM World) α)
    (input : ι) (initialWorld : World),
    CodecLaw codec → Supported (program input) →
    ∃ requiredFuel : Nat, ∀ fuel : Nat, requiredFuel ≤ fuel →
      runReplay blobs fuel program input initialWorld =
        runDirect blobs program input initialWorld

end LeanCloud.Proofs
