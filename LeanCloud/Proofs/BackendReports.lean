import LeanCloud.Proofs.BackendProgress
import LeanCloud.Proofs.BackendWakeup
import LeanCloud.Proofs.BranchAncestry

namespace LeanCloud.Backend.Proofs.Journal
open Lean LeanCloud.Proofs JournalDb JournalAdapter ReplayRecovery

def OpenReport (source : Location) (before after : Backend.State) : Prop :=
  ∃ parent index, ∃ outcome : Exit, ∃ checked, Location.ReportsTo source parent index ∧
    Grows before checked ∧ Grows checked after ∧
    view checked (childKey parent.key index) = some (toJson outcome) ∧
    ∀ value, ¬ CompletedAt (view checked) parent.key value

theorem OpenReport.grow {source before after initial final}
    (report : OpenReport source before after) (earlier : Grows initial before) (later : Grows after final) :
    OpenReport source initial final := by
  obtain ⟨parent, index, outcome, checked, linked, started, finished, child, incomplete⟩ := report
  exact ⟨parent, index, outcome, checked, linked, earlier.trans started, finished.trans later, child, incomplete⟩

theorem OpenReport.descendant {source middle before after}
    (report : OpenReport middle before after) (enters : middle.entersChild source = true) :
    OpenReport source before after := by
  obtain ⟨parent, index, outcome, checked, linked, rest⟩ := report
  exact ⟨parent, index, outcome, checked, linked.descendant enters, rest⟩

theorem OpenReport.of_next {source before after} (report : OpenReport source.next before after) :
    OpenReport source before after := by
  obtain ⟨parent, index, outcome, checked, linked, rest⟩ := report
  exact ⟨parent, index, outcome, checked, linked.of_next, rest⟩

theorem OpenReport.child_cases {source before after index}
    (report : OpenReport (source.child index) before after) :
    (∃ outcome, Notification source index outcome before after (.runnable #[])) ∨ OpenReport source before after := by
  obtain ⟨parent, childIndex, outcome, checked, linked, started, finished, child, incomplete⟩ := report
  rcases linked.child_cases with ⟨rfl, rfl⟩ | enclosing
  · exact .inl ⟨outcome, .waiting checked started finished child incomplete⟩
  · exact .inr ⟨parent, childIndex, outcome, checked, enclosing, started, finished, child, incomplete⟩

/-- Resolve the missing children of a partial fork. If every child reports to
an incomplete group, at least one reports to an outer group: all of this fork's
missing children cannot return empty notifications after their known siblings. -/
theorem OpenReport.fork {current : Location} {before after : Backend.State} {slots : Array (Option Exit)}
    (ordered : Ordered after)
    (published : JournalAdapter.Published (records current.key (.suspended slots)) (view before))
    (settled : Result.settle slots = .suspended slots)
    (children : ∀ i : Fin slots.size, slots[i] = none → OpenReport (current.child i.val) before after) :
    OpenReport current before after := by
  classical
  apply Classical.byContradiction
  intro absent
  have candidates (i : Fin slots.size) : ∃ outcome,
      slots[i] = some outcome ∨
        (slots[i] = none ∧ Notification current i.val outcome before after (.runnable #[])) := by
    cases stored : slots[i] with
    | some outcome => exact ⟨outcome, .inl rfl⟩
    | none =>
      rcases (children i stored).child_cases with ⟨outcome, notified⟩ | outer
      · exact ⟨outcome, .inr ⟨rfl, notified⟩⟩
      · exact False.elim (absent outer)
  let outcomes := Array.ofFn fun i => (candidates i).choose
  let known := fun i : Fin outcomes.size => slots[i.val]! ≠ none
  have descriptor : view before (forkKey current.key) = some (toJson outcomes.size) := by
    simpa [outcomes] using (published_fork published).1
  have recorded (i : Fin outcomes.size) (present : known i) :
      view before (childKey current.key i.val) = some (toJson outcomes[i]) := by
    let j : Fin slots.size := ⟨i.val, by simpa [outcomes] using i.isLt⟩
    rcases (candidates j).choose_spec with stored | ⟨missing, _⟩
    · apply (published_fork published).2 i.val j.isLt
      simpa [outcomes, getElem!_pos, j.isLt, j] using stored
    · exact False.elim (present (by simpa [getElem!_pos, j.isLt, j] using missing))
  have missing : ∃ i, ¬ known i := by
    obtain ⟨index, inside, empty⟩ := Array.mem_iff_getElem.mp (Result.settle_suspended_missing settled)
    refine ⟨⟨index, by simpa [outcomes] using inside⟩, ?_⟩
    simp [known, getElem!_pos, inside, empty]
  have notified (i : Fin outcomes.size) (missing : ¬ known i) :
      Notification current i.val outcomes[i] before after (.runnable #[]) := by
    let j : Fin slots.size := ⟨i.val, by simpa [outcomes] using i.isLt⟩
    rcases (candidates j).choose_spec with stored | ⟨_, report⟩
    · apply False.elim
      apply missing
      intro empty
      have impossible : slots[j] = none := by simpa [getElem!_pos, j.isLt, j] using empty
      rw [stored] at impossible
      cases impossible
    · simpa [outcomes, j] using report
  obtain ⟨i, _, impossible⟩ := missing_notifications_wake current outcomes before after ordered descriptor
    known recorded missing (fun _ => .runnable #[]) notified
  simp at impossible

/-- If every successor ultimately reports to an incomplete enclosing group,
the incoming command must do the same. A fork cannot strand itself by letting
all of its missing children acknowledge empty responses. -/
theorem StepProgress.open_report {tree current node before after initial final response}
    (ordered : Ordered final)
    (progress : StepProgress tree current node before response after)
    (earlier : Grows initial before) (executed : Grows before after) (later : Grows after final)
    (unfinished : ∀ outcome, response ≠ .done outcome)
    (reports : ∀ locations, response = .runnable locations →
      ∀ location ∈ locations, OpenReport location after final) : OpenReport current initial final := by
  have started := earlier.trans executed
  cases progress with
  | command command =>
    cases command with
    | finished finished =>
      cases linked : current.parent? with
      | none =>
        have done : response = .done node.exit := by simpa only [Finished, linked] using finished.2
        exact False.elim (unfinished _ done)
      | some pair =>
        obtain ⟨parent, index⟩ := pair
        have notified : Notification parent index node.exit before after response := by
          simpa only [Finished, linked] using finished.2
        cases notified with
        | wake outcome completed =>
          exact ((reports _ rfl parent (by simp)).descendant (Location.ReportsTo.of_parent linked).2.1).grow started (.refl _)
        | waiting checked first last child incomplete =>
          exact ⟨parent, index, node.exit, checked, .of_parent linked,
            earlier.trans first, last.trans later, child, incomplete⟩
    | @initialized children result next count after size checked first last noResult noFork published =>
      by_cases empty : count = 0
      · exact (reports _ rfl current (by simp [empty])).grow started (.refl _)
      · have contains : none ∈ (Array.replicate count none : Array (Option Exit)) := by simp [empty]
        rw [Result.settle_missing _ contains] at published
        apply OpenReport.grow (earlier := started) (later := Grows.refl _)
        apply OpenReport.fork ordered published (Result.settle_missing _ contains)
        intro i _
        apply reports _ rfl
        simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ↓reduceIte]
        exact Array.mem_ofFn.mpr ⟨⟨i.val, by simpa using i.isLt⟩, rfl⟩
    | @waiting children result next count after size slots slotSize checked first last incomplete settled published =>
      apply OpenReport.grow (earlier := started) (later := Grows.refl _)
      apply OpenReport.fork ordered published settled
      intro i missing
      apply reports _ rfl
      apply Array.mem_filterMap.mpr
      refine ⟨i.val, Array.mem_ofFn.mpr ⟨⟨i.val, by omega⟩, rfl⟩, ?_⟩
      have empty : slots[i.val]! = none := by simpa [getElem!_pos, i.isLt] using missing
      simp only [empty, Option.isNone_none, ↓reduceIte]
    | joined completed => exact (reports _ rfl current.next (by simp)).of_next.grow started (.refl _)
  | redirect redirected =>
    obtain ⟨ancestor, children, result, next, route, active, completed, enters, work⟩ := redirected
    exact ((reports _ work ancestor (by simp)).descendant enters).grow started (.refl _)
  | parent parent index outcome linked completed work =>
    exact ((reports _ work parent (by simp)).descendant (Location.ReportsTo.of_parent linked).2.1).grow started (.refl _)

end LeanCloud.Backend.Proofs.Journal
