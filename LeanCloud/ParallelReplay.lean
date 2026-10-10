import LeanCloud.ReplayModel

namespace LeanCloud.ParallelReplay
open ReplayModel

/-- Keep the records even when a child exhausts its interpreter budget.
Workflow failures are recorded outcomes, not errors of this driver. -/
def mergeChildren (children : List (Except CloudError Unit × Journal)) : ExceptT CloudError M Unit := do
  let journal ← get
  let merged ← liftExcept (merge journal (children.flatMap Prod.snd))
  set merged
  children.forM fun (outcome, _) => liftExcept outcome

/-- Read the old journal and return only new records, including partial writes
when fuel runs out. Immutable lists share the old tail without copying it. -/
def worker (resume : Assignment → ExceptT CloudError M Unit)
    (old : Journal) (assignment : Assignment) : Except CloudError Unit × Journal :=
  let (outcome, journal) := (resume assignment).run old
  (outcome, newRecords old journal)

/-- Spawn the whole batch against one read-only journal. Each task returns its
own additions; union them before resuming the parent. -/
def children (resume : Assignment → ExceptT CloudError M Unit)
    (assignments : List Assignment) : ExceptT CloudError M Unit := do
  let snapshot ← get
  let tasks := assignments.map fun assignment =>
    Task.spawn fun () => worker resume snapshot assignment
  mergeChildren (tasks.map Task.get)

def follow (resume : Assignment → ExceptT CloudError M Unit)
    (branch : Location) : Progress → ExceptT CloudError M Unit
  | .done => pure ()
  | .fork location count => do
      children resume ((List.range count).map fun index => ⟨0, location.child index⟩)
      resume ⟨0, branch⟩

/-- The same replay step as the sequential driver. Children contribute disjoint
new records before the parent resumes and records the join. -/
def run [Codec α] (blobs : BlobStorage M) (source : Cloud M α) : Nat → Assignment → ExceptT CloudError M Unit
  | 0, _ => throw ⟨.protocol, "Parallel replay fuel exhausted"⟩
  | fuel + 1, assignment => do
      let progress ← ReplayInterpreter.step store blobs (fuel + 1) (fun _ : Unit => source) () assignment
      follow (run blobs source fuel) assignment.branchStart progress

def interpret [Codec α] (fuel : Nat) (program : ι → Cloud M α) (input : ι) : ExceptT CloudError M α := do
  run noBlobs (program input) fuel ⟨0, Location.root⟩
  let some outcome ← store.outcome | throw ⟨.protocol, "Missing root result"⟩
  ReplayInterpreter.result outcome

end LeanCloud.ParallelReplay
