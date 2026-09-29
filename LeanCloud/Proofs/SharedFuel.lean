import LeanCloud.Proofs.SharedLoop
import LeanCloud.Proofs.ReplayFuel

/-! Exact fuel independence in the combined journal/leased-queue backend.
Extra traversal fuel changes neither observations nor physical crash points. -/

namespace LeanCloud.Proofs.SharedRecovery
open Lean CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

theorem step_fuel_eq {source : Cloud (CrashModel.M Journal) Json} {tree target node}
    (expansion : Expansion source tree) (supported : PureProgram source)
    (route : TreeRoute tree Location.root target node)
    (start : State Durable) (valid : Valid tree start.durable) (activated : route.Activated start.durable.1)
    (blobs : BlobStorage Worker M)
    (worker : Worker) (first second : Nat)
    (enoughFirst : route.prefixSteps + 1 ≤ first) (enoughSecond : route.prefixSteps + 1 ≤ second) :
    ((step workerDb blobs first (journalMap.program source) target).run worker).run start =
      ((step workerDb blobs second (journalMap.program source) target).run worker).run start := by
  rw [step_eq blobs first source supported target worker,
    step_eq blobs second source supported target worker, run_map, run_map]
  have same := route.step_fuel_same expansion supported start.durable.1 valid.1 valid.2.1 activated
    noBlobs first second enoughFirst enoughSecond ⟨start.durable.1, start.faults⟩ rfl
  simp only [withLeft, ExceptT.run]
  dsimp only [ExceptT.run] at same
  rw [same]

/-- One common budget suffices for every selected location. This is equality
of whole iterations, including an identical crash or the identical final state,
not merely equality of successful workflow outcomes. -/
theorem iteration_fuel_eq {source : Cloud (CrashModel.M Journal) Json} {tree}
    (expansion : Expansion source tree) (supported : PureProgram source)
    (blobs : BlobStorage Worker M)
    (worker : Worker) (first second : Nat) (enoughFirst : sizeOf tree ≤ first) (enoughSecond : sizeOf tree ≤ second)
    (start : State Durable) (valid : Valid tree start.durable) :
    ((iteration workerDb blobs queue first (journalMap.program source)).run worker).run start =
      ((iteration workerDb blobs queue second (journalMap.program source)).run worker).run start := by
  have checked := next_spec expansion worker start valid
  rw [iteration_eq, iteration_eq, run_bind, run_bind]
  generalize polled : (queue.next worker).run start = observed at *
  obtain ⟨result, current⟩ := observed
  cases result with
  | error crash => rfl
  | ok returned =>
    obtain ⟨work, delivered⟩ := returned
    obtain ⟨validNow, _, ready⟩ := checked.2
    cases work with
    | idle | completed => rfl
    | item location =>
      obtain ⟨node, route, activated, _⟩ := ready location rfl
      dsimp only
      rw [report_eq, report_eq, run_map, run_map, run_bind, run_bind]
      rw [step_fuel_eq expansion supported route current validNow activated blobs delivered first second
        (Nat.le_trans route.fuel_bound enoughFirst) (Nat.le_trans route.fuel_bound enoughSecond)]

end LeanCloud.Proofs.SharedRecovery
