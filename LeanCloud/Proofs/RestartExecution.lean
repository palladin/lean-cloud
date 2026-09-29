import LeanCloud.Proofs.ClockedReplay

/-! A finite prefix of actual loop observations is executed by the public
driver and its existing restart boundary. Loop fuel decreases within an attempt;
a crash resets it to the original budget and retains the committed state. -/

namespace LeanCloud.Proofs.SharedRecovery
open Lean CrashModel CrashRecovery JournalAdapter ReplayInterpreter.Internal

/-- Connect finite observations to the actual driver. Completion is a premise
only of this operational lemma; trace liveness supplies it below. -/
theorem observations_recovers [Codec α] (source : Cloud M Json)
    (blobs : BlobStorage Worker M) (work : WorkQueue Worker M)
    (states : Nat → State Durable)
    (results : Nat → Except Crash (Except CloudError (Option Exit) × Worker))
    (traversal : Nat) (outcome : Exit)
    (observed : ∀ n fuel, traversal ≤ fuel →
      ((iteration workerDb blobs work fuel source).run ⟨(), none⟩).run (states n) =
        (results n, states (n + 1)))
    (sound : ∀ n, results n = .error .stopped ∨
      results n = .ok (.ok none, (⟨(), none⟩ : Worker)) ∨
      results n = .ok (.ok (some outcome), (⟨(), none⟩ : Worker)))
    (stop : Nat) (completed : results stop = .ok (.ok (some outcome), (⟨(), none⟩ : Worker))) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ final,
      Recovers ((run (α := α) workerDb blobs work fuel source).run ⟨(), none⟩)
        (states 0) (ReplayModel.decodeExit outcome, (⟨(), none⟩ : Worker)) final := by
  have segment (count : Nat) : ∀ n full fuel,
      results (n + count) = .ok (.ok (some outcome), (⟨(), none⟩ : Worker)) →
      traversal + count + 1 ≤ full → traversal + count + 1 ≤ fuel →
      ∃ final,
        ((run (α := α) workerDb blobs work fuel source).run ⟨(), none⟩).run (states n) =
          (.ok (ReplayModel.decodeExit outcome, (⟨(), none⟩ : Worker)), final) ∨
        ∃ committed,
          ((run (α := α) workerDb blobs work fuel source).run ⟨(), none⟩).run (states n) =
            (.error .stopped, committed) ∧
          Recovers ((run (α := α) workerDb blobs work full source).run ⟨(), none⟩)
            committed (ReplayModel.decodeExit outcome, (⟨(), none⟩ : Worker)) final := by
    induction count with
    | zero =>
      intro n full fuel finished _ enough
      cases fuel with
      | zero => omega
      | succ fuel =>
        refine ⟨states (n + 1), .inl ?_⟩
        rw [run_iteration_eq, observed n (fuel + 1) (by omega)]
        have returned : results n = .ok (.ok (some outcome), (⟨(), none⟩ : Worker)) := by simpa using finished
        rw [returned]
    | succ count ih =>
      intro n full fuel finished fullEnough enough
      have later : results ((n + 1) + count) = .ok (.ok (some outcome), (⟨(), none⟩ : Worker)) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 count] using finished
      cases fuel with
      | zero => omega
      | succ fuel =>
        have unfolded := run_iteration_eq (α := α) workerDb blobs work fuel source ⟨(), none⟩ (states n)
        rw [observed n (fuel + 1) (by omega)] at unfolded
        rcases sound n with crashed | unfinished | returned
        · rw [crashed] at unfolded
          obtain ⟨final, returned | ⟨committed, stopped, recovered⟩⟩ :=
            ih (n + 1) full full later (by omega) (by omega)
          · exact ⟨final, .inr ⟨states (n + 1), unfolded, .returned returned⟩⟩
          · exact ⟨final, .inr ⟨states (n + 1), unfolded, .crashed stopped recovered⟩⟩
        · rw [unfinished] at unfolded
          obtain ⟨final, returned | ⟨committed, stopped, recovered⟩⟩ :=
            ih (n + 1) full fuel later (by omega) (by omega)
          · exact ⟨final, .inl (unfolded.trans returned)⟩
          · exact ⟨final, .inr ⟨committed, unfolded.trans stopped, recovered⟩⟩
        · rw [returned] at unfolded
          exact ⟨states (n + 1), .inl unfolded⟩
  refine ⟨traversal + stop + 1, ?_⟩
  intro fuel enough
  obtain ⟨final, returned | ⟨committed, stopped, recovered⟩⟩ :=
    segment stop 0 fuel fuel (by simpa using completed) enough enough
  · exact ⟨final, .returned returned⟩
  · exact ⟨final, .crashed stopped recovered⟩

/-- Fair delivery and finite physical crashes suffice for the actual public
loop to recover. Completion is derived from the program, not assumed. -/
theorem Trace.run_eventually_restart [Codec α] {source tree blobs} (trace : Trace source blobs)
    (expansion : Expansion source tree) (supported : PureProgram source)
    (comparable : ReplayRecovery.Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (elapsed : State Durable → Nat) (clocked : trace.Clocked elapsed)
    (enough : ∀ n, sizeOf tree ≤ trace.fuel n)
    (valid : Valid tree (trace.states 0).durable) (covered : Covered tree (trace.states 0).durable)
    (fair : trace.FairDelivery) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ final retryBound, ∀ retries, retryBound ≤ retries →
      (CrashM.restart retries ((run (α := α) workerDb blobs (clockedQueue elapsed)
        fuel (journalMap.program source)).run ⟨(), none⟩)).run (trace.states 0) =
          (.ok (ReplayModel.decodeExit tree.exit, (⟨(), none⟩ : Worker)), final) := by
  have kept n := trace.invariants expansion supported comparable sameExit enough valid covered n
  have sound n : trace.result n = .error .stopped ∨
      trace.result n = .ok (.ok none, (⟨(), none⟩ : Worker)) ∨
      trace.result n = .ok (.ok (some tree.exit), (⟨(), none⟩ : Worker)) := by
    have checked := (trace.round expansion supported comparable sameExit n (enough n) (kept n).1 (kept n).2).2.2.2
    cases observed : trace.result n with
    | error crash => cases crash; exact .inl rfl
    | ok returned =>
      rw [observed] at checked
      obtain ⟨completed, rfl, correct⟩ := checked
      cases completed with
      | none => exact .inr (.inl rfl)
      | some outcome =>
        have same := correct outcome rfl
        subst outcome
        exact .inr (.inr rfl)
  obtain ⟨stop, completed⟩ := trace.eventually_returns expansion supported comparable sameExit enough valid covered fair
  obtain ⟨bound, recovers⟩ := observations_recovers (α := α) (journalMap.program source) blobs
    (clockedQueue elapsed) trace.states trace.result (sizeOf tree) tree.exit
    (fun n fuel sufficient => trace.iteration_at expansion supported elapsed clocked n fuel (enough n) sufficient (kept n).1)
    sound stop completed
  refine ⟨bound, ?_⟩
  intro fuel sufficient
  obtain ⟨final, recovered⟩ := recovers fuel sufficient
  obtain ⟨retryBound, finished⟩ := recovered.eventually_restart
  exact ⟨final, retryBound, finished⟩

end LeanCloud.Proofs.SharedRecovery
