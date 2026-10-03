import LeanCloud.Proofs.BackendRank

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanCloud.Proofs JournalAdapter JournalDb ReplayRecovery
open LeanCloud.Proofs.ConcurrentJournal (rank)

/-- An intermediate property of a stable suffix. Fair scheduling must derive
these responses from the actual code; this is not a queue or Db assumption. -/
def StableResponses (tree : ExecutionTree) (state : Backend.State) (available : Location → Prop) : Prop :=
  ∀ current, available current → ∃ node, ∃ _route : TreeRoute tree Location.root current node,
    ∃ before after locations,
      view before = view state ∧ view after = view state ∧ Grows before after ∧ Ordered after ∧
      StepProgress tree current node before (.runnable locations) after ∧
      Emits tree (.runnable locations) after ∧ ∀ target ∈ locations, available target

private noncomputable def closedAt (state : Backend.State) (location : Location) : Bool := by
  classical
  exact decide (∃ outcome, CompletedAt (view state) location.key outcome)

/-- A stable journal admits no infinite chain of useful response work. The
well-founded measure depends only on the finite pure program, not queue order. -/
theorem StableResponses.reported {tree state available} (responses : StableResponses tree state available)
    (current : Location) (ready : available current) : OpenReport current state state := by
  classical
  obtain ⟨node, route, before, after, locations, first, last, growth, ordered, progress, emitted, supplied⟩ := responses current ready
  have correct location : closedAt state location = true ↔ ∃ outcome, CompletedAt (view after) location.key outcome := by
    rw [last]
    simp [closedAt]
  have reports (target : Location) (member : target ∈ locations) : OpenReport target after after := by
    have decreases := progress.rank_decreases route emitted (first.trans last.symm) (closedAt state) correct target member
    exact (responses.reported target (supplied target member)).fixed last.symm last.symm
  have reported := progress.open_report ordered (.refl _) growth (.refl _)
    (by intro outcome impossible; cases impossible) (by
      intro children same target member
      cases same
      exact reports target member)
  exact reported.fixed first last
termination_by rank tree (closedAt state) current
decreasing_by exact decreases

/-- The physical journal may grow forever with duplicate writes. Its visible
contents stabilize because the pure program has finitely many immutable keys. -/
theorem eventually_stable (tree : ExecutionTree) (states : Nat → Backend.State)
    (valid : ∀ time, Valid (tree.journal Location.root) (states time))
    (growth : ∀ first last, first ≤ last → Grows (states first) (states last)) :
    ∃ cut, ∀ time, cut ≤ time → view (states time) = view (states cut) := by
  apply finite_journal_stable (fun time => view (states time)) ((tree.records Location.root).map Prod.fst)
  · intro first last later
    exact (growth first last later).reads
  · intro time key value recorded
    have bound := valid time key value recorded
    have member := (tree.journal_read_iff Location.root (by simp [Location.root]) key value).mp bound
    exact List.mem_map.mpr ⟨(key, value), member, rfl⟩

end LeanCloud.Backend.Proofs.Journal
