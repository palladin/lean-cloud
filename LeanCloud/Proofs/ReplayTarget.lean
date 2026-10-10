import LeanCloud.Coordination
import LeanCloud.Proofs.Location

namespace LeanCloud.Proofs

/-- A proof-only position inside a branch. The executable replay step receives
only the branch start and discovers its progress from the journal. -/
structure ReplayTarget where
  branchStart : Location
  location : Location

def ReplayTarget.work (target : ReplayTarget) : Assignment := ⟨0, target.branchStart⟩

instance : Coe ReplayTarget Assignment := ⟨ReplayTarget.work⟩

end LeanCloud.Proofs
