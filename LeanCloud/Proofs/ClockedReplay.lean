import LeanCloud.Proofs.SharedLiveness
import LeanCloud.Proofs.SharedFuel
import LeanCloud.Proofs.ReplayExecution

/-! Time advancement belongs to the queue environment. This proof adapter
advances time before a poll and delegates to the existing leased queue. The
public interpreter and restart runner are unchanged. -/

namespace LeanCloud.Proofs.SharedRecovery
open Lean CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

/-- An environment supplies elapsed time for each observed poll. The policy
may depend on the current model state; fairness is a separate obligation. -/
def clockedQueue (elapsed : State Durable → Nat) : WorkQueue Worker M where
  next worker := fun start => (queue.next worker).run (advanceState (elapsed start) start)
  complete := queue.complete

theorem clocked_iteration_eq (elapsed : State Durable → Nat) (source : Cloud M Json)
    (blobs : BlobStorage Worker M) (fuel : Nat) (worker : Worker) (start : State Durable) :
    ((iteration workerDb blobs (clockedQueue elapsed) fuel source).run worker).run start =
      ((iteration workerDb blobs queue fuel source).run worker).run (advanceState (elapsed start) start) := by
  rw [iteration_eq, iteration_eq, run_bind, run_bind]
  rfl

def Trace.Clocked {source blobs} (trace : Trace source blobs) (elapsed : State Durable → Nat) : Prop :=
  ∀ n, trace.elapsed n = elapsed (trace.states n)

/-- Construct the actual observations of this environment with a fixed ample
traversal budget. No completion, fairness, or successful attempt is assumed. -/
theorem clocked_trace_exists (source : Cloud (CrashModel.M Journal) Json) (blobs : BlobStorage Worker M)
    (elapsed : State Durable → Nat) (fuel : Nat) (start : State Durable) :
    ∃ trace : Trace source blobs, trace.states 0 = start ∧ trace.Clocked elapsed ∧ ∀ n, trace.fuel n = fuel := by
  let next (state : State Durable) :=
    (((iteration workerDb blobs queue fuel (journalMap.program source)).run ⟨(), none⟩).run
      (advanceState (elapsed state) state)).2
  let states : Nat → State Durable := fun n => Nat.rec start (fun _ state => next state) n
  exact ⟨⟨states, fun n => elapsed (states n), fun _ => fuel, fun _ => rfl⟩, rfl, fun _ => rfl, fun _ => rfl⟩

/-- The same trace is observed by every sufficient iteration budget, including
the decreasing budgets passed by the public replay loop. -/
theorem Trace.iteration_at {source tree blobs} (trace : Trace source blobs)
    (expansion : Expansion source tree) (supported : PureProgram source)
    (elapsed : State Durable → Nat) (clocked : trace.Clocked elapsed)
    (n fuel : Nat)
    (traceEnough : sizeOf tree ≤ trace.fuel n) (enough : sizeOf tree ≤ fuel)
    (valid : Valid tree (trace.states n).durable) :
    ((iteration workerDb blobs (clockedQueue elapsed) fuel (journalMap.program source)).run ⟨(), none⟩).run
      (trace.states n) = (trace.result n, trace.states (n + 1)) := by
  rw [clocked_iteration_eq, ← clocked n]
  exact (iteration_fuel_eq expansion supported blobs ⟨(), none⟩ fuel (trace.fuel n) enough traceEnough
    (advanceState (trace.elapsed n) (trace.states n)) (valid_advance valid _)).trans (trace.execution n)

theorem result_returned [codec : Codec α] (outcome : Exit) (worker : Worker) (start : State Durable) :
    ((result (m := StateT Worker M) (α := α) outcome).run worker).run start =
      (.ok (ReplayModel.decodeExit outcome, worker), start) := by
  cases outcome with
  | success value =>
    cases decoded : codec.decode value <;> simp [result, decode, ReplayModel.decodeExit, decoded] <;> rfl
  | failure error => rfl
  | cancelled reason => rfl

/-- One unfolding of the actual public driver. Ordinary workflow errors are
returned; a base-monad crash escapes with the committed state. -/
theorem run_iteration_eq [Codec α] (backend : Db Worker M) (blobs : BlobStorage Worker M)
    (work : WorkQueue Worker M) (fuel : Nat) (source : Cloud M Json) (worker : Worker) (start : State Durable) :
    ((run (α := α) backend blobs work (fuel + 1) source).run worker).run start =
      match ((iteration backend blobs work (fuel + 1) source).run worker).run start with
      | (.error crash, final) => (.error crash, final)
      | (.ok (.error error, worker), final) => (.ok (.error error, worker), final)
      | (.ok (.ok none, worker), final) => ((run (α := α) backend blobs work fuel source).run worker).run final
      | (.ok (.ok (some outcome), worker), final) => (.ok (ReplayModel.decodeExit outcome, worker), final) := by
  rw [run_succ_eq]
  change ((iteration backend blobs work (fuel + 1) source).run worker >>= fun returned =>
    ((ExceptT.bindCont (fun outcome => match outcome with
      | some outcome => result (α := α) outcome
      | none => run backend blobs work fuel source) returned.1).run returned.2)).run start = _
  rw [run_bind]
  cases observed : ((iteration backend blobs work (fuel + 1) source).run worker).run start with
  | mk returned final =>
    cases returned with
    | error crash => rfl
    | ok value =>
      obtain ⟨outcome, worker⟩ := value
      cases outcome with
      | error error => rfl
      | ok finished =>
        cases finished with
        | none => rfl
        | some outcome => exact result_returned outcome worker final

end LeanCloud.Proofs.SharedRecovery
