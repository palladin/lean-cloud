import LeanCloud.WorkQueue
import Init.Omega

/-! Selection laws for an environment's execution history. These are obligations
on repeated queue polls, not properties implied by `Monad m`. An implementation
must show that its histories satisfy the laws; this file does not certify an
arbitrary backend. The history assumes workers keep polling and each poll returns.
One round includes a poll and any processing before the next poll. -/

namespace LeanCloud.Proofs.WorkQueue

structure Trace where
  /-- Pending work immediately before poll `n`. -/
  pending : Nat → Location → Prop
  response : Nat → Work

def Trace.selected (trace : Trace) (n : Nat) : Option Location :=
  match trace.response n with
  | .item location => some location
  | .completed _ | .idle => none

/-- Weak fairness: work that stays pending cannot be ignored forever.
This permits temporary idle responses and gives no fixed waiting-time bound. -/
def Fair (trace : Trace) : Prop :=
  ∀ location start,
    (∀ n, start ≤ n → trace.pending n location) →
    ∃ n, start ≤ n ∧ trace.selected n = some location

structure Laws (trace : Trace) : Prop where
  selects_pending : ∀ n location,
    trace.selected n = some location → trace.pending n location
  retains_unselected : ∀ n location,
    trace.pending n location → trace.selected n ≠ some location → trace.pending (n + 1) location
  completed_empty : ∀ n outcome,
    trace.response n = .completed outcome → ∀ location, ¬ trace.pending n location
  fair : Fair trace

/-- Retention plus weak fairness implies no starvation for every pending item,
even though fairness itself only mentions continuously pending items. -/
theorem eventually_selected {trace : Trace} (laws : Laws trace) (location : Location)
    (start : Nat) (pending : trace.pending start location) :
    ∃ n, start ≤ n ∧ trace.selected n = some location := by
  apply Classical.byContradiction
  intro never
  have notSelected : ∀ n, start ≤ n → trace.selected n ≠ some location := by
    intro n after selected
    exact never ⟨n, after, selected⟩
  have staysOffset (offset : Nat) : trace.pending (start + offset) location := by
    induction offset with
    | zero => exact pending
    | succ offset ih =>
      exact laws.retains_unselected (start + offset) location ih (notSelected _ (by omega))
  have stays : ∀ n, start ≤ n → trace.pending n location := by
    intro n after
    simpa only [show start + (n - start) = n by omega] using staysOffset (n - start)
  exact never (laws.fair location start stays)

/-- Every finite snapshot of pending locations is served within some common
finite number of polls. Newly published items get the same guarantee from their
own publication point. This asserts selection, not successful effect execution. -/
theorem all_pending_selected {trace : Trace} (laws : Laws trace) (start : Nat)
    (locations : List Location) (pending : ∀ location ∈ locations, trace.pending start location) :
    ∃ stop, start ≤ stop ∧ ∀ location ∈ locations,
      ∃ n, start ≤ n ∧ n < stop ∧ trace.selected n = some location := by
  induction locations with
  | nil => exact ⟨start, Nat.le_refl _, by simp⟩
  | cons location rest ih =>
    obtain ⟨n, after, selected⟩ := eventually_selected laws location start (pending _ (by simp))
    obtain ⟨stop, stopAfter, served⟩ := ih (fun item member => pending item (by simp [member]))
    refine ⟨max (n + 1) stop, by omega, ?_⟩
    intro item member
    rcases List.mem_cons.mp member with same | member
    · subst item
      exact ⟨n, after, by omega, selected⟩
    · obtain ⟨k, kAfter, before, selected⟩ := served item member
      exact ⟨k, kAfter, by omega, selected⟩

/-- A nonempty pending set rules out an infinite suffix of idle responses. -/
theorem cannot_idle_forever {trace : Trace} (laws : Laws trace) (location : Location)
    (start : Nat) (pending : trace.pending start location) :
    ¬ (∀ n, start ≤ n → trace.response n = .idle) := by
  intro idle
  obtain ⟨n, after, selected⟩ := eventually_selected laws location start pending
  simp [Trace.selected, idle n after] at selected

end LeanCloud.Proofs.WorkQueue
