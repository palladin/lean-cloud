import LeanCloud.Proofs.RecoveryDriver

namespace LeanCloud.Proofs.RecoveryCompletion
open ReplayFaults ReplayModel JournalMerge RecoveryStep RecoveryBatch RecoveryProgress RecoveryDriver

private theorem fault_bound (workers : List (Location × Faults)) : ∃ limit, FaultBound limit workers := by
  induction workers with
  | nil => exact ⟨0, by simp [FaultBound]⟩
  | cons entry rest ih =>
    obtain ⟨limit, bounded⟩ := ih
    refine ⟨max entry.2.remaining.length limit, ?_⟩
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (bounded other member) (Nat.le_max_right _ _)

variable [codec : Codec α] (source : Cloud WorkerM α)

/-- Empty storage and arbitrary finite worker fault scripts suffice: all replay
cursors, expected records, and fuel bounds are constructed from pure evaluation. -/
theorem finishes_from_empty {outcome} (evaluation : Pure.Evaluation source outcome) (plan : Plan) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ after,
      (RestartingParallelReplay.run source fuel [⟨0, Location.root⟩]).run (Saved.initial plan) =
        (.ok [Parallel.recorded codec.encode outcome], after) ∧
      after.journal.lookup (ReplayStore.returnKey Location.root) =
        some ⟨ReplayStore.returnRequest, Parallel.recorded codec.encode outcome⟩ := by
  obtain ⟨expected, complete, known⟩ := Specification.workflow_journal_exists evaluation codec.encode
  obtain ⟨budget, meaning⟩ := RecoveryMeaning.of_complete complete
  obtain ⟨faults, bounded⟩ := fault_bound (Saved.initial plan).workers
  have ready : Ready source expected budget [] Location.root :=
    ⟨α, codec.encode, source, outcome, Location.root, 0, budget, by simp, by simp,
      RecoveryCursor.Cursor.root, meaning, known⟩
  have valid : Invariant expected faults (Saved.initial plan) := ⟨by simp [Unique, Saved.initial], .empty _, bounded⟩
  refine ⟨budget + faults + rank expected [] budget 1 + 2, fun fuel enough => ?_⟩
  obtain ⟨outcomes, after, finished, _, _, returned⟩ := run_correct source fuel (Saved.initial plan)
    [⟨0, Location.root⟩] 1 valid (by simp [Separate])
    (by intro a ha; rw [List.mem_singleton.mp ha]; exact ready)
    (by intro a ha; rw [List.mem_singleton.mp ha]; decide) enough
  cases returned with
  | cons present canonical rest =>
    cases rest
    have same := Option.some.inj (canonical.symm.trans known)
    have value := congrArg ReplayRecord.outcome same
    dsimp only at value
    exact ⟨after, by simpa only [value] using finished, by simpa only [value] using present⟩

/-- The actual restarting driver returns the specified value or application
error. Crashes do not become Cloud errors and do not change the answer. -/
theorem evaluates_from_empty {outcome} (evaluation : Pure.Evaluation source outcome)
    (roundtrip : Pure.RoundTrips codec) (plan : Plan) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      ((RestartingParallelReplay.interpret fuel (fun _ : Unit => source) ()).run (Saved.initial plan)).1 = outcome := by
  obtain ⟨bound, finishes⟩ := finishes_from_empty source evaluation plan
  refine ⟨bound, fun fuel enough => ?_⟩
  obtain ⟨after, finished, _⟩ := finishes fuel enough
  simp only [RestartingParallelReplay.interpret, StateT.run, bind_run, finished]
  cases outcome with
  | ok value => simp [ReplayInterpreter.result, Parallel.recorded, ReplayInterpreter.Internal.decode, roundtrip value]
  | error error => rfl

end LeanCloud.Proofs.RecoveryCompletion
