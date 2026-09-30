import LeanCloud.Proofs.ConcurrentFinish

/-! Concurrent child completions cannot all return an empty notification.
The latest post-publication reread sees every child's durable slot. The ideal
database's write log orders these observations without assuming snapshot reads,
fixed replies, or an atomic operation spanning publication and reread. -/

namespace LeanCloud.Proofs.ConcurrentJournal
open Lean Simulation SimulationBackend JournalAdapter JournalDb ReplayRecovery

private theorem Grows.between {first middle last : Durable}
    (a : Grows first last) (b : Grows middle last)
    (length : first.records.length ≤ middle.records.length) : Grows first middle := by
  have suffix := List.suffix_of_suffix_length_le a.2 b.2 length
  refine ⟨?_, suffix⟩
  obtain ⟨written, records⟩ := suffix
  intro key value stored
  have lookup : view middle key = (written.lookup key).or (view first key) := by
    simp only [view, ← records, List.lookup_append]
  cases found : written.lookup key with
  | none => simpa [found, stored] using lookup
  | some actual =>
    have present : view middle key = some actual := by simpa [found] using lookup
    have same := (b key actual present).symm.trans (a key value stored)
    exact present.trans same

private theorem Grows.latest {count : Nat} (nonempty : 0 < count)
    (observed : Fin count → Durable) (final : Durable)
    (before : ∀ i, Grows (observed i) final) :
    ∃ latest, ∀ i, Grows (observed i) (observed latest) := by
  let lengths := List.ofFn fun i => (observed i).records.length
  have nonnil : lengths ≠ [] := by
    intro empty
    have := congrArg List.length empty
    simp [lengths] at this
    omega
  obtain ⟨latest, largest⟩ := List.mem_ofFn.mp (List.max_mem nonnil)
  refine ⟨latest, fun i => (before i).between (before latest) ?_⟩
  rw [largest]
  exact List.le_max_of_mem (l := lengths) (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- All children have returned a notification for this parent. At least one
must request it. Different children, and different retries, may return different
responses; an empty response carries its own earlier incomplete reread. -/
theorem notifications_wake (parent : Location) (outcomes : Array Exit)
    (nonempty : 0 < outcomes.size) (before final : Durable)
    (descriptor : view before (forkKey parent.key) = some (toJson outcomes.size))
    (responses : Fin outcomes.size → StepResult)
    (notified : ∀ i, Notification parent i.val outcomes[i] before final (responses i)) :
    ∃ i, responses i = .runnable #[parent] := by
  classical
  by_cases missing : ∃ i, responses i = .runnable #[parent]
  · exact missing
  apply False.elim
  have waiting : ∀ i : Fin outcomes.size, ∃ checked,
      Grows before checked ∧ Grows checked final ∧
      view checked (childKey parent.key i.val) = some (toJson outcomes[i]) ∧
      ∀ result, ¬ CompletedAt (view checked) parent.key result := by
    intro i
    have h := notified i
    generalize response : responses i = answer at h
    cases h with
    | wake result completed => exact False.elim (missing ⟨i, response⟩)
    | waiting checked started finished child incomplete =>
      exact ⟨checked, started, finished, child, incomplete⟩
  let checked i := (waiting i).choose
  have started i := (waiting i).choose_spec.1
  have finished i := (waiting i).choose_spec.2.1
  have child i := (waiting i).choose_spec.2.2.1
  have incomplete i := (waiting i).choose_spec.2.2.2
  obtain ⟨latest, ordered⟩ := Grows.latest nonempty checked final finished
  have settled : ∃ result, Result.settle (outcomes.map some) = .completed result := by
    rw [Result.settle_completed]
    split <;> exact ⟨_, rfl⟩
  obtain ⟨result, settled⟩ := settled
  apply incomplete latest result
  refine .group (outcomes.map some) ?_ ?_ settled
  · simpa using started latest _ _ descriptor
  · intro index inside
    have bound : index < outcomes.size := by simpa using inside
    exact ⟨outcomes[index], by simp [getElem!_pos, bound], ordered ⟨index, bound⟩ _ _ (child ⟨index, bound⟩)⟩

/-- A partial read only republishes missing children. Children already present
at that publication point need no new notification. The remaining nonempty set
still cannot all return empty: its latest reread also sees the earlier slots. -/
theorem missing_notifications_wake (parent : Location) (outcomes : Array Exit)
    (before final : Durable)
    (descriptor : view before (forkKey parent.key) = some (toJson outcomes.size))
    (known : Fin outcomes.size → Prop)
    (recorded : ∀ i, known i → view before (childKey parent.key i.val) = some (toJson outcomes[i]))
    (missing : ∃ i, ¬ known i)
    (responses : Fin outcomes.size → StepResult)
    (notified : ∀ i, ¬ known i → Notification parent i.val outcomes[i] before final (responses i)) :
    ∃ i, ¬ known i ∧ responses i = .runnable #[parent] := by
  classical
  by_cases woken : ∃ i, ¬ known i ∧ responses i = .runnable #[parent]
  · exact woken
  apply False.elim
  obtain ⟨index, absent⟩ := missing
  have wait : ∃ checked, Grows before checked ∧ Grows checked final ∧
      ∀ outcome, ¬ CompletedAt (view checked) parent.key outcome := by
    have result := notified index absent
    generalize equal : responses index = response at result
    cases result with
    | wake outcome complete => exact False.elim (woken ⟨index, absent, equal⟩)
    | waiting checked started later _ incomplete => exact ⟨checked, started, later, incomplete⟩
  obtain ⟨checked, started, later, incomplete⟩ := wait
  let allResponses i := if known i then .runnable #[] else responses i
  have allNotified i : Notification parent i.val outcomes[i] before final (allResponses i) := by
    dsimp only [allResponses]
    split
    · rename_i present
      exact .waiting before (.refl _) (started.trans later) (recorded i present)
        (fun outcome complete => incomplete outcome (complete.grow started.1))
    · rename_i absent
      exact notified i absent
  obtain ⟨i, wake⟩ := notifications_wake parent outcomes (Nat.zero_lt_of_lt index.isLt)
    before final descriptor allResponses allNotified
  by_cases present : known i
  · simp [allResponses, present] at wake
  · exact woken ⟨i, present, by simpa [allResponses, present] using wake⟩

/-- Actual child `finish` calls under any finite legal interleaving, including
crashes, lost replies, and fresh retries. If each child has a returned attempt,
one of those attempts requests the parent. This proves notification, not queue
publication or eventual completion of the attempts. -/
theorem finish_children_wake (expected : Journal) (parent : Location) (outcomes : Array Exit)
    (nonempty : 0 < outcomes.size) (locations : Fin outcomes.size → Location)
    (linked : ∀ i, (locations i).parent? = some (parent, i.val))
    (format : ∀ i, Readable expected (locations i).key)
    (coherent : ∀ i, Coherent expected (locations i).key)
    (comparable : Comparable expected)
    (sameExit : ∀ i : Fin outcomes.size, (outcomes[i] == outcomes[i]) = true)
    (intended : ∀ i, expected (resultKey (locations i).key) = some (toJson outcomes[i]))
    (parentFormat : Readable expected parent.key) (parentCoherent : Coherent expected parent.key)
    (prescribed : ∀ i : Fin outcomes.size, expected (childKey parent.key i.val) = some (toJson outcomes[i]))
    (initial : Durable) (bounded : Valid expected initial)
    (descriptor : view initial (forkKey parent.key) = some (toJson outcomes.size))
    (source : ∀ i, CompletionSource (view initial) expected (locations i).key outcomes[i])
    (events : List (Event outcomes.size))
    (final : Simulation.State Durable (Except CloudError StepResult × Unit) outcomes.size)
    (executed :
      let start := fun i => (ReplayInterpreter.Internal.finish (JournalDb.ofDb rawDb) (locations i) outcomes[i]).run ()
      Simulation.run start advance events (Simulation.State.initial initial start) = .ok final)
    (returned : ∀ i, ∃ value, (final.workers i).outcome? = some value) :
    ∃ i, (final.workers i).outcome? = some (.ok (.runnable #[parent]), ()) := by
  have parents i next index (relation : (locations i).parent? = some (next, index)) :
      ParentReady expected next index outcomes[i] initial := by
    rw [linked i] at relation
    cases relation
    exact ⟨outcomes.size, i.isLt, descriptor, prescribed i, parentFormat, parentCoherent⟩
  have safe := finish_concurrent expected locations (fun i => outcomes[i]) format coherent comparable
    sameExit intended initial bounded source parents events final executed
  have replies : ∀ i, ∃ response,
      (final.workers i).outcome? = some (.ok response, ()) ∧
      Notification parent i.val outcomes[i] initial final.durable response := by
    intro i
    obtain ⟨value, done⟩ := returned i
    obtain ⟨response, same, finished⟩ := safe.2.2 i value done
    refine ⟨response, by simpa [same] using done, ?_⟩
    simpa only [Finished, linked i] using finished.2
  let responses i := (replies i).choose
  obtain ⟨i, wake⟩ := notifications_wake parent outcomes nonempty initial final.durable descriptor
    responses (fun i => (replies i).choose_spec.2)
  exact ⟨i, by simpa only [← wake] using (replies i).choose_spec.1⟩

end LeanCloud.Proofs.ConcurrentJournal
