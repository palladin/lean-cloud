import LeanCloud.Proofs.WorkQueue

/-! Fairness gives eventual selection, while progress gives eventual completion.
The ranking function counts remaining work, including work not yet published by
forks. It is not the number of pending queue items (forks can increase that).
FairDriver constructs this ranking for actual replay execution from the program's
finite direct evaluation and exact snapshot-work accounting. -/

namespace LeanCloud.Proofs.WorkQueue

structure Progress (trace : Trace) where
  remaining : Nat → Nat
  /-- Processing a selected item makes strict progress. -/
  decreases : ∀ n location, trace.selected n = some location → remaining (n + 1) < remaining n
  /-- Polls which select nothing cannot add work. -/
  does_not_increase : ∀ n, remaining (n + 1) ≤ remaining n
  /-- Unfinished work always has a pending item; it cannot silently disappear. -/
  has_pending : ∀ n, 0 < remaining n → ∃ location, trace.pending n location

theorem Progress.monotone {trace : Trace} (progress : Progress trace) (start stop : Nat)
    (after : start ≤ stop) : progress.remaining stop ≤ progress.remaining start := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le after
  induction offset with
  | zero => exact Nat.le_refl _
  | succ offset ih =>
    have step := progress.does_not_increase (start + offset)
    simpa only [Nat.add_assoc] using Nat.le_trans step (ih (by omega))

/-- Every fair trace satisfying finite progress eventually exhausts its work.
The bound depends on the trace; fairness gives no uniform bound on idle polls. -/
theorem eventually_finished {trace : Trace} (laws : Laws trace) (progress : Progress trace)
    (start : Nat) : ∃ stop, start ≤ stop ∧ progress.remaining stop = 0 := by
  generalize size : progress.remaining start = remaining
  induction remaining using Nat.strongRecOn generalizing start with
  | ind remaining ih =>
    by_cases zero : remaining = 0
    · exact ⟨start, Nat.le_refl _, size.trans zero⟩
    · obtain ⟨location, pending⟩ := progress.has_pending start (by omega)
      obtain ⟨selectedAt, after, selected⟩ := eventually_selected laws location start pending
      have less : progress.remaining (selectedAt + 1) < remaining := by
        have := progress.decreases selectedAt location selected
        have := progress.monotone start selectedAt after
        omega
      obtain ⟨stop, later, finished⟩ := ih _ less (selectedAt + 1) rfl
      exact ⟨stop, by omega, finished⟩

end LeanCloud.Proofs.WorkQueue
