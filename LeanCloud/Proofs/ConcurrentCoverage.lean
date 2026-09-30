import LeanCloud.Proofs.ConcurrentProgress
import LeanCloud.Proofs.CoverageReplacement

/-! Coverage supplied by a command response, including stale mixed reads. This
accounts for the selected branch; global coverage must additionally track who
is responsible for waking a parent when its last child becomes durable. -/

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean Simulation SimulationBackend JournalAdapter JournalDb ReplayRecovery

/-- Missing physical slots are represented by available children. If the fork
has completed concurrently, any available child instead wakes its join. -/
private theorem fork_covered {m : Type → Type u} {program : Cloud m Json}
    {tree current children result next journal available done}
    (whole : Expansion program tree)
    (route : TreeRoute tree Location.root current (.fork children result next))
    (bounded : Extends journal (tree.journal Location.root))
    (descriptor : journal (forkKey current.key) = some (toJson children.length))
    (missing : ∀ i : Fin children.length, journal (childKey current.key i.val) = none → available (current.child i.val))
    (wake : ∃ i : Fin children.length, available (current.child i.val)) :
    Coverage journal available (.fork children result next) current done := by
  have rootSize : 0 < Location.root.size := by simp [Location.root]
  rcases whole.fork_coverage_cases rootSize route.member journal bounded descriptor with
    ⟨uncached, absent⟩ | completed
  · refine .waiting descriptor uncached absent ?_
    intro i
    cases stored : journal (childKey current.key i.val) with
    | none => exact .queued (missing i stored) (.here _)
    | some value =>
      have same := (bounded _ _ stored).symm.trans ((tree.fork_fields rootSize route.member).2.2 i)
      cases same
      exact .reported (.inl stored)
  · obtain ⟨i, ready⟩ := wake
    exact .queued ready (.parent (Location.parent_child current (route.nonempty rootSize) i.val) completed (.here _))

private theorem missing_available {current : Location} {count : Nat} {slots : Array (Option Exit)}
    {available : Location → Prop} (supplied : ∀ location ∈
      ((Array.ofFn fun i : Fin count => i.val).filterMap fun i =>
        if slots[i]!.isNone then some (current.child i) else none), available location)
    (i : Nat) (inside : i < count) (empty : slots[i]! = none) : available (current.child i) := by
  apply supplied
  apply Array.mem_filterMap.mpr
  exact ⟨i, Array.mem_ofFn.mpr ⟨⟨i, inside⟩, rfl⟩, by simp [empty]⟩

/-- Once a response's successors are available (or its root result is
published), they cover its original command. A partial read need not equal
the journal at return time: already-recorded children are discharged, missing
ones are enqueued, and any completed fork can be woken by an emitted child. -/
theorem CommandProgress.coverage {m : Type → Type u} {program : Cloud m Json}
    {tree current node before response after rootDone available}
    (whole : Expansion program tree) (route : TreeRoute tree Location.root current node)
    (bounded : Valid (tree.journal Location.root) after)
    (progress : CommandProgress current before node response after)
    (supplied : ResponseAvailable rootDone available response) :
    Coverage (view after) available node current (BranchReported (view after) rootDone node current) := by
  cases progress with
  | finished recorded =>
    apply Coverage.reported
    cases linked : current.parent? with
    | none =>
      have response : response = .done node.exit := by simpa only [Finished, linked] using recorded.2
      simpa only [BranchReported, linked, response, ResponseAvailable] using supplied
    | some pair =>
      obtain ⟨parent, index⟩ := pair
      have notified : Notification parent index node.exit before after response := by
        simpa only [Finished, linked] using recorded.2
      simp only [BranchReported, linked]
      cases notified with
      | wake outcome completed => exact .inr ⟨outcome, completed⟩
      | waiting checked started later child incomplete => exact .inl (later _ _ child)
  | @initialized children result next count after size checked started later noResult noFork published =>
    by_cases empty : count = 0
    · exact .queued (supplied current (by simp [empty])) (.here _)
    · have missing : none ∈ (Array.replicate count none : Array (Option Exit)) := by simp [empty]
      rw [Result.settle_missing _ missing] at published
      simp only [ResponseAvailable, beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ↓reduceIte] at supplied
      have descriptor : view after (forkKey current.key) = some (toJson children.length) := by
        simpa only [Array.size_replicate, size] using (published_fork published).1
      apply fork_covered whole route bounded descriptor
      · intro i _
        exact supplied (current.child i.val) (Array.mem_ofFn.mpr ⟨⟨i.val, by omega⟩, rfl⟩)
      · have positive : 0 < children.length := by omega
        refine ⟨⟨0, positive⟩, ?_⟩
        exact supplied (current.child 0) (Array.mem_ofFn.mpr ⟨⟨0, by omega⟩, rfl⟩)
  | @waiting children result next count after size slots slotSize checked started later incomplete settled published =>
    have descriptor : view after (forkKey current.key) = some (toJson children.length) := by
      simpa only [slotSize, size] using (published_fork published).1
    apply fork_covered whole route bounded descriptor
    · intro i absent
      have inside : i.val < slots.size := by omega
      have empty : slots[i.val]! = none := by
        cases found : slots[i.val]! with
        | none => rfl
        | some value =>
          have stored := (published_fork published).2 i.val inside value found
          simp [absent] at stored
      exact missing_available supplied i.val (by omega) empty
    · obtain ⟨i, inside, empty⟩ := Array.mem_iff_getElem.mp (Result.settle_suspended_missing settled)
      exact ⟨⟨i, by omega⟩, missing_available supplied i (by omega) (by simpa [getElem!_pos, inside] using empty)⟩
  | joined completed => exact .continued completed (.queued (supplied current.next (by simp)) (.here _))

private theorem CommandProgress.empty_finished {current before node response after}
    (progress : CommandProgress current before node response after) (empty : response = .runnable #[]) :
    Finished current node.exit before (.runnable #[]) after := by
  cases progress with
  | finished recorded => simpa only [empty] using recorded
  | @initialized children result next count after size checked started later noResult noFork published =>
    by_cases zero : count = 0
    · simp [zero] at empty
    · simp only [beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ↓reduceIte] at empty
      have size := congrArg (fun response => match response with
        | .runnable locations => locations.size
        | .done _ => 0) empty
      simp only [Array.size_ofFn, Array.size_empty] at size
      exact False.elim (zero size)
  | @waiting children result next count after size slots slotSize checked started later incomplete settled published =>
    have supplied : ResponseAvailable False (fun _ => False)
        (.runnable ((Array.ofFn fun i : Fin count => i.val).filterMap fun i =>
          if slots[i]!.isNone then some (current.child i) else none)) := by
      rw [empty]
      intro location member
      simp at member
    obtain ⟨i, inside, missing⟩ := Array.mem_iff_getElem.mp (Result.settle_suspended_missing settled)
    exact False.elim (missing_available supplied i (by omega) (by simpa [getElem!_pos, inside] using missing))
  | joined completed => simp at empty

/-- Dropping a delivery without successors is justified only by a completed
child whose reread began before its parent completed. It cannot be an empty
fork-publication response, a join, a root completion, or an ancestor redirect. -/
theorem StepProgress.empty_notification {tree current node before response after}
    (progress : StepProgress tree current node before response after) (empty : response = .runnable #[]) :
    ∃ parent index checked, current.parent? = some (parent, index) ∧
      Grows before checked ∧ Grows checked after ∧
      view checked (childKey parent.key index) = some (toJson node.exit) ∧
      ∀ outcome, ¬ CompletedAt (view checked) parent.key outcome := by
  have finished : Finished current node.exit before (.runnable #[]) after := by
    cases progress with
    | command progress => exact progress.empty_finished empty
    | redirect redirected =>
      obtain ⟨location, children, result, next, route, active, complete, enters, work⟩ := redirected
      simp [empty] at work
    | parent parent index outcome linked completed work => simp [empty] at work
  cases linked : current.parent? with
  | none => simp [Finished, linked] at finished
  | some pair =>
    obtain ⟨parent, index⟩ := pair
    have notified : Notification parent index node.exit before after (.runnable #[]) := by
      simpa only [Finished, linked] using finished.2
    cases notified with
    | waiting checked started later child incomplete => exact ⟨parent, index, checked, rfl, started, later, child, incomplete⟩

end LeanCloud.Proofs.ConcurrentJournal
