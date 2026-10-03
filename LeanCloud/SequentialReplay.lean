import LeanCloud.ReplayInterpreter

namespace LeanCloud.SequentialReplay

/-- A reference driver: finish each child in source order, then resume its parent.
Every assignment reconstructs the original program through `ReplayInterpreter.step`.
The store is the only state carried between assignments. -/
def follow [Monad m] (resume : Assignment → ExceptT CloudError m Unit)
    (branch : Location) : Progress → ExceptT CloudError m Unit
  | .done => pure ()
  | .fork location count => do
      (List.range count).forM fun index => resume ⟨0, location.child index, location.child index, false⟩
      resume ⟨0, branch, location, true⟩

def run [Monad m] [Codec α] (store : ReplayStore m) (blobs : BlobStorage m)
    (source : Cloud m α) : Nat → Assignment → ExceptT CloudError m Unit
  | 0, _ => throw ⟨.protocol, "Sequential replay fuel exhausted"⟩
  | fuel + 1, assignment => do
      let progress ← ReplayInterpreter.step store blobs (fuel + 1) (fun _ : Unit => source) () assignment
      follow (run store blobs source fuel) assignment.branch progress

/-- Return the workflow result, including its recorded application failure. -/
def interpret [Monad m] [Codec α] (store : ReplayStore m) (blobs : BlobStorage m)
    (fuel : Nat) (program : ι → Cloud m α) (input : ι) : ExceptT CloudError m α := do
  run store blobs (program input) fuel ⟨0, Location.root, Location.root, false⟩
  let some outcome ← store.outcome | throw ⟨.protocol, "Missing root result"⟩
  ReplayInterpreter.result outcome

end LeanCloud.SequentialReplay
