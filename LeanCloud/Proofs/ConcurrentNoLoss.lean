import LeanCloud.Proofs.ConcurrentTransfer
import LeanCloud.Proofs.ConcurrentWakeup
import LeanCloud.Proofs.BranchAncestry

/-! Accounting for joins in the finite publication graph. If a branch retires
without publishing work, it has reported a child result to a still-incomplete
enclosing group. Missing children cannot all end this way at the same fork. -/

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean Simulation SimulationBackend JournalDb JournalAdapter ReplayRecovery

def OpenReport (source : Location) (before after : Durable) : Prop :=
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
theorem OpenReport.fork {current : Location} {before after : Durable} {slots : Array (Option Exit)}
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
  obtain ⟨i, _, impossible⟩ := missing_notifications_wake current outcomes before after descriptor
    known recorded missing (fun _ => .runnable #[]) notified
  simp at impossible

/-- If every successor ultimately reports to an incomplete enclosing group,
the incoming command must do the same. A fork cannot strand itself by letting
all of its missing children acknowledge empty responses. -/
theorem StepProgress.open_report {tree current node before after initial final response}
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
        apply OpenReport.fork published (Result.settle_missing _ contains)
        intro i _
        apply reports _ rfl
        simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ↓reduceIte]
        exact Array.mem_ofFn.mpr ⟨⟨i.val, by simpa using i.isLt⟩, rfl⟩
    | @waiting children result next count after size slots slotSize checked first last incomplete settled published =>
      apply OpenReport.grow (earlier := started) (later := Grows.refl _)
      apply OpenReport.fork published settled
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

end LeanCloud.Proofs.ConcurrentJournal

namespace LeanCloud.Proofs.ConcurrentAudit
open Lean Simulation SimulationBackend ReplayRecovery
open ConcurrentHandoff (Log)

/-- A retained message whose enclosing-branch result has not already been
reported to a still-incomplete group. Completed groups may still need a
continuation wakeup, so their messages remain outstanding. -/
def Outstanding (state : Durable) : Prop :=
  ∃ slot : Nat, ∃ message : LeaseQueueModel.Message Location,
    state.transport.messages[slot]? = some (some message) ∧
    ¬ ConcurrentJournal.OpenReport message.value state state

/-- An unfinished workflow retains outstanding work, not just duplicates of
results already reported to incomplete groups. The proof follows actual
publication slots: if every retained item and retired branch had such a report,
the root would have to report to an enclosing branch, which does not exist. -/
theorem Valid.no_loss {tree : ExecutionTree} {final : Log} (valid : Valid tree final)
    (initialized : History.Grows ⟨SimulationBackend.initial, []⟩ final) :
    final.current.completed = some tree.exit ∨ Outstanding final.current := by
  classical
  by_cases pending : Outstanding final.current
  · exact .inr pending
  cases completed : final.current.completed with
  | some outcome =>
    have same := valid.1.completed outcome completed
    exact .inl (congrArg some same)
  | none =>
    apply False.elim
    let property := fun slot source => ∀ checkpoint, BeforeSlot checkpoint slot final →
      ConcurrentJournal.OpenReport source checkpoint.current final.current
    have live (slot : Nat) (message : LeaseQueueModel.Message Location)
        (held : final.current.transport.messages[slot]? = some (some message)) :
        property slot message.value := by
      intro checkpoint before
      have report : ConcurrentJournal.OpenReport message.value final.current final.current := by
        apply Classical.byContradiction
        intro unreported
        exact pending ⟨slot, message, held, unreported⟩
      exact report.grow (valid.growth before.1 (.refl _)).journal (.refl _)
    have retired slot location node started finished acknowledged response
        (_route : TreeRoute tree Location.root location node)
        (executed : History.Grows started finished) (later : History.Grows finished acknowledged)
        (recorded : History.Grows acknowledged final) (inside : slot < started.current.transport.messages.size)
        (progress : ConcurrentJournal.StepProgress tree location node started.current response finished.current)
        (published : ConcurrentHandoff.Published finished.past.length response acknowledged)
        (successors : Successors property finished.current.transport.messages.size response) : property slot location := by
      intro checkpoint before
      have history := later.trans recorded
      have begun := before.2 started (executed.trans history) inside
      apply progress.open_report (valid.growth begun (executed.trans history)).journal
        (valid.growth executed history).journal (valid.growth history (.refl _)).journal
      · intro outcome same
        rw [same] at published
        have stored := valid.published_done recorded published
        rw [completed] at stored
        cases stored
      · intro locations same target member
        rw [same] at successors
        obtain ⟨next, fresh, resolve⟩ := successors target member
        exact resolve finished (BeforeSlot.fresh valid history fresh)
    have root := valid.induct_work property live retired initialized
      (slot := 0) (message := ⟨Location.root, 0, 0⟩) (by rfl)
    obtain ⟨parent, index, outcome, checked, linked, _⟩ :=
      root ⟨SimulationBackend.initial, []⟩ (BeforeSlot.initial initialized 0)
    exact Location.ReportsTo.not_root linked

/-- Every finite legal schedule of the real interpreter retains outstanding
work or has published the original workflow's final outcome. Leased items count
as retained; crashes and lost replies do not remove this recovery obligation. -/
theorem attempts_no_loss [codec : Codec α] (program : ι → Cloud M α) (input : ι)
    {tree : ExecutionTree} (whole : Expansion (codec.encode <$> program input) tree)
    (supported : PureProgram (program input))
    (comparable : Comparable (tree.journal Location.root))
    (sameExit : ∀ location node, (location, node) ∈ tree.nodes Location.root → (node.exit == node.exit) = true)
    (duration : Nat) (fuel : Fin count → Nat) (events : List (Event count))
    (final : Simulation.State Durable (Except CloudError α × SimulationBackend.Worker) count)
    (executed :
      let start := fun worker => attempt (fuel worker) duration program input
      Simulation.run start SimulationBackend.advance events
        (Simulation.State.initial SimulationBackend.initial start) = .ok final) :
    final.durable.completed = some tree.exit ∨ Outstanding final.durable := by
  obtain ⟨past, growth, valid, _, _⟩ := attempts_certified program input whole supported comparable sameExit
    duration fuel events final executed
  exact valid.no_loss growth.2

end LeanCloud.Proofs.ConcurrentAudit
