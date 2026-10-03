import LeanCloud.Proofs.BackendReports
import LeanCloud.Proofs.BackendStep
import LeanCloud.Proofs.ConcurrentRank

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanCloud.Proofs JournalAdapter JournalDb ReplayRecovery
open LeanCloud.Proofs.ConcurrentJournal (rank ancestors ancestors_child ancestors_next rank_forward rank_redirect)

private theorem fixed_checkpoint {before checked after : Backend.State}
    (started : Grows before checked) (later : Grows checked after) (fixed : view before = view after) :
    view checked = view after :=
  JournalAdapter.Extends.antisymm later.reads (by rw [← fixed]; exact started.reads)

/-- When the journal is fixed, every emitted location strictly decreases the
finite progress measure. Fork initialization cannot occur without a new record;
an incomplete fork exposes children, a join advances, and stale work wakes a
completed ancestor. Duplicate delivery does not change any of these facts. -/
theorem StepProgress.rank_decreases {tree current node before after locations}
    (route : TreeRoute tree Location.root current node)
    (progress : StepProgress tree current node before (.runnable locations) after)
    (emitted : Emits tree (.runnable locations) after)
    (fixed : view before = view after) (closed : Location → Bool)
    (correct : ∀ location, closed location = true ↔ ∃ outcome, CompletedAt (view after) location.key outcome)
    (target : Location) (member : target ∈ locations) :
    Prod.Lex (· < ·) (· < ·) (rank tree closed target) (rank tree closed current) := by
  have first : current ∈ (tree.nodes Location.root).map Prod.fst := List.mem_map.mpr ⟨_, route.member, rfl⟩
  have last : target ∈ (tree.nodes Location.root).map Prod.fst := by
    obtain ⟨node, route, _⟩ := emitted target member
    exact List.mem_map.mpr ⟨_, route.member, rfl⟩
  cases progress with
  | command progress =>
    cases progress with
    | finished recorded =>
      cases linked : current.parent? with
      | none => simp [Finished, linked] at recorded
      | some pair =>
        obtain ⟨parent, index⟩ := pair
        have notification : Notification parent index node.exit before after (.runnable locations) := by
          simpa only [Finished, linked] using recorded.2
        cases notification with
        | wake outcome complete =>
          have same : target = parent := by simpa using member
          subst target
          exact rank_redirect tree (Location.ReportsTo.of_parent linked).2.1 ((correct parent).mpr ⟨outcome, complete⟩)
        | waiting => simp at member
    | initialized size checked started later noResult noFork published =>
      have same := fixed_checkpoint started later fixed
      rw [same] at noResult noFork
      exact False.elim (initialized_changes ⟨noResult, noFork⟩ published rfl)
    | waiting size slots slotSize checked started later incomplete settled published =>
      have same := fixed_checkpoint started later fixed
      rw [same] at incomplete
      have openGroup : closed current = false := by
        cases found : closed current with
        | false => rfl
        | true =>
          obtain ⟨outcome, complete⟩ := (correct current).mp found
          exact False.elim (incomplete outcome complete)
      obtain ⟨index, _, selected⟩ := Array.mem_filterMap.mp member
      split at selected
      · cases selected
        apply rank_forward first last
        · simp [ancestors_child, openGroup]
        · exact Location.earlier_child current index
      · cases selected
    | joined complete =>
      have same : target = current.next := by simpa using member
      subst target
      exact rank_forward first last (ancestors_next closed current)
        (Location.earlier_next current (route.nonempty (by simp [Location.root])))
  | redirect redirected =>
    obtain ⟨parent, children, result, next, parentRoute, active, complete, enters, work⟩ := redirected
    cases work
    have same : target = parent := by simpa using member
    subst target
    exact rank_redirect tree enters ((correct parent).mpr ⟨_, complete⟩)
  | parent parent index outcome linked complete work =>
    cases work
    have same : target = parent := by simpa using member
    subst target
    exact rank_redirect tree (Location.ReportsTo.of_parent linked).2.1 ((correct parent).mpr ⟨outcome, complete⟩)

/-- Collapse an older notification witness to the fixed visible journal.
Physical logs and queue contents need not be equal. -/
theorem OpenReport.fixed {source : Location} {before after state : Backend.State}
    (report : OpenReport source before after) (first : view before = view state) (last : view after = view state) :
    OpenReport source state state := by
  obtain ⟨parent, index, outcome, checked, linked, started, later, child, incomplete⟩ := report
  have same := fixed_checkpoint started later (first.trans last.symm)
  rw [same, last] at child incomplete
  exact ⟨parent, index, outcome, state, linked, .refl _, .refl _, child, incomplete⟩

end LeanCloud.Backend.Proofs.Journal
