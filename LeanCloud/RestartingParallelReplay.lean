import LeanCloud.ReplayFaults

/-! Parallel replay with worker-local restart. Scheduling handles reports only;
worker code owns every replay-store operation, including final-result reads. -/

namespace LeanCloud.RestartingParallelReplay
open ReplayFaults

abbrev M := WorkerM

/-- Finish the children of a suspended worker, then assign its branch again.
All retry handling is inside `workers`; scheduling has no crash mechanism. -/
def run [Codec α] (source : Cloud M α) : Nat → List Assignment → Backend (List Exit)
  | 0, _ => throw ⟨.protocol, "Parallel replay scheduler fuel exhausted"⟩
  | fuel + 1, assignments => do
      let reports ← workers source (fuel + 1) assignments
      let outcomes ← reports.mapM fun (assignment, report) => do
        match report with
        | .done outcome => return [outcome]
        | .fork location count =>
            let _ ← run source fuel ((List.range count).map fun index => ⟨0, location.child index⟩)
            run source fuel [assignment]
      return outcomes.flatten

/-- Return the root worker's reply. The coordinator does not read the journal. -/
def interpret [Codec α] (fuel : Nat) (program : ι → Cloud M α) (input : ι) :
    StateM Saved (Except CloudError α) := (do
  let [outcome] ← run (program input) fuel [⟨0, Location.root⟩]
    | throw ⟨.protocol, "Expected one root worker reply"⟩
  ReplayInterpreter.result outcome
  : Backend α).run

end LeanCloud.RestartingParallelReplay
